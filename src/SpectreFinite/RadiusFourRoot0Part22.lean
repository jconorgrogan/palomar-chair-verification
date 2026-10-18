module

public import SpectreFinite.RadiusFourRoot0Part21
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node64Domains0 : Domains 61 State := restrict root0Node63Domains1 45 (5,5)
def root0Node64Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
  | 4 => some [(2,1)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node64Domains0_fast_eq : root0Node64Domains0 = expandDomains root0Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node64Domains0 v = expandDomains root0Node64Domains0Fast v from by decide) v
def root0Node64Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0)]
  | 4 => [(2,1)]
  | 5 => [(8,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(5,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5)]
  | 49 => [(7,0)]
  | 50 => [(1,4)]
  | 51 => [(0,5)]
  | 52 => [(4,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(6,0)]
  | 57 => [(7,1)]
  | 58 => [(7,5)]
  | 59 => [(6,0)]
  | _ => [(7,1)]
def root0Node64Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
  | 4 => some [(2,1)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5)]
  | 49 => some [(7,0)]
  | 50 => some [(1,4)]
  | 51 => some [(0,5)]
  | 52 => some [(4,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,0)]
  | 57 => some [(7,1)]
  | 58 => some [(7,5)]
  | 59 => some [(6,0)]
  | _ => some [(7,1)]
theorem root0Node64Domains1_fast_eq : root0Node64Domains1 = expandDomains root0Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node64Domains1 v = expandDomains root0Node64Domains1Fast v from by decide) v
theorem root0Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root0Node64Domains0 root0Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node64Domains0 root0Node64Domains1
    root0Node64Domains0Fast root0Node64Domains1Fast
    root0Node64Domains0_fast_eq root0Node64Domains1_fast_eq (by decide)
theorem root0Node64Step1_checked :
    checkReplacement table46 root0Node64Domains0 root0Node64Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node64Step1Chunk0_0_checked, root0Node64Step1Chunk0_1_checked, root0Node64Step1Chunk0_2_checked, root0Node64Step1Chunk0_3_checked, root0Node64Step1Chunk0_4_checked, root0Node64Step1Chunk0_5_checked, root0Node64Step1Chunk1_0_checked, root0Node64Step1Chunk1_1_checked, root0Node64Step1Chunk1_2_checked, root0Node64Step1Chunk1_3_checked, root0Node64Step1Chunk1_4_checked, root0Node64Step1Chunk1_5_checked, root0Node64Step1Chunk2_0_checked, root0Node64Step1Chunk2_1_checked, root0Node64Step1Chunk2_2_checked, root0Node64Step1Chunk2_3_checked, root0Node64Step1Chunk2_4_checked, root0Node64Step1Chunk2_5_checked, root0Node64Step1Chunk3_0_checked, root0Node64Step1Chunk3_1_checked, root0Node64Step1Chunk3_2_checked, root0Node64Step1Chunk3_3_checked, root0Node64Step1Chunk3_4_checked, root0Node64Step1Chunk3_5_checked, root0Node64Step1Chunk4_0_checked, root0Node64Step1Chunk4_1_checked, root0Node64Step1Chunk4_2_checked, root0Node64Step1Chunk4_3_checked, root0Node64Step1Chunk4_4_checked, root0Node64Step1Chunk4_5_checked, root0Node64Step1Chunk5_0_checked, root0Node64Step1Chunk5_1_checked, root0Node64Step1Chunk5_2_checked, root0Node64Step1Chunk5_3_checked, root0Node64Step1Chunk5_4_checked, root0Node64Step1Chunk5_5_checked, root0Node64Step1Chunk6_0_checked, root0Node64Step1Chunk6_1_checked, root0Node64Step1Chunk6_2_checked, root0Node64Step1Chunk6_3_checked, root0Node64Step1Chunk6_4_checked, root0Node64Step1Chunk6_5_checked, root0Node64Step1Chunk7_0_checked, root0Node64Step1Chunk7_1_checked, root0Node64Step1Chunk7_2_checked, root0Node64Step1Chunk7_3_checked, root0Node64Step1Chunk7_4_checked, root0Node64Step1Chunk7_5_checked, root0Node64Step1Chunk8_0_checked, root0Node64Step1Chunk8_1_checked, root0Node64Step1Chunk8_2_checked, root0Node64Step1Chunk8_3_checked, root0Node64Step1Chunk8_4_checked, root0Node64Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node64Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node64Domains1 (.output 31) = true := by decide
def root0Node65Domains0 : Domains 61 State := restrict root0Node63Domains1 45 (8,5)
def root0Node65Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
  | 4 => some [(2,1)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node65Domains0_fast_eq : root0Node65Domains0 = expandDomains root0Node65Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node65Domains0 v = expandDomains root0Node65Domains0Fast v from by decide) v
def root0Node65Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0)]
  | 4 => [(2,1)]
  | 5 => [(8,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(7,0)]
  | 50 => [(3,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2)]
  | _ => [(1,1)]
def root0Node65Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
  | 4 => some [(2,1)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(3,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2)]
  | _ => some [(1,1)]
theorem root0Node65Domains1_fast_eq : root0Node65Domains1 = expandDomains root0Node65Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node65Domains1 v = expandDomains root0Node65Domains1Fast v from by decide) v
theorem root0Node65Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root0Node65Domains0 root0Node65Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node65Domains0 root0Node65Domains1
    root0Node65Domains0Fast root0Node65Domains1Fast
    root0Node65Domains0_fast_eq root0Node65Domains1_fast_eq (by decide)
theorem root0Node65Step1_checked :
    checkReplacement table46 root0Node65Domains0 root0Node65Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node65Step1Chunk0_0_checked, root0Node65Step1Chunk0_1_checked, root0Node65Step1Chunk0_2_checked, root0Node65Step1Chunk0_3_checked, root0Node65Step1Chunk0_4_checked, root0Node65Step1Chunk0_5_checked, root0Node65Step1Chunk1_0_checked, root0Node65Step1Chunk1_1_checked, root0Node65Step1Chunk1_2_checked, root0Node65Step1Chunk1_3_checked, root0Node65Step1Chunk1_4_checked, root0Node65Step1Chunk1_5_checked, root0Node65Step1Chunk2_0_checked, root0Node65Step1Chunk2_1_checked, root0Node65Step1Chunk2_2_checked, root0Node65Step1Chunk2_3_checked, root0Node65Step1Chunk2_4_checked, root0Node65Step1Chunk2_5_checked, root0Node65Step1Chunk3_0_checked, root0Node65Step1Chunk3_1_checked, root0Node65Step1Chunk3_2_checked, root0Node65Step1Chunk3_3_checked, root0Node65Step1Chunk3_4_checked, root0Node65Step1Chunk3_5_checked, root0Node65Step1Chunk4_0_checked, root0Node65Step1Chunk4_1_checked, root0Node65Step1Chunk4_2_checked, root0Node65Step1Chunk4_3_checked, root0Node65Step1Chunk4_4_checked, root0Node65Step1Chunk4_5_checked, root0Node65Step1Chunk5_0_checked, root0Node65Step1Chunk5_1_checked, root0Node65Step1Chunk5_2_checked, root0Node65Step1Chunk5_3_checked, root0Node65Step1Chunk5_4_checked, root0Node65Step1Chunk5_5_checked, root0Node65Step1Chunk6_0_checked, root0Node65Step1Chunk6_1_checked, root0Node65Step1Chunk6_2_checked, root0Node65Step1Chunk6_3_checked, root0Node65Step1Chunk6_4_checked, root0Node65Step1Chunk6_5_checked, root0Node65Step1Chunk7_0_checked, root0Node65Step1Chunk7_1_checked, root0Node65Step1Chunk7_2_checked, root0Node65Step1Chunk7_3_checked, root0Node65Step1Chunk7_4_checked, root0Node65Step1Chunk7_5_checked, root0Node65Step1Chunk8_0_checked, root0Node65Step1Chunk8_1_checked, root0Node65Step1Chunk8_2_checked, root0Node65Step1Chunk8_3_checked, root0Node65Step1Chunk8_4_checked, root0Node65Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node65Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node65Domains1 (.output 32) = true := by decide
def root0Node66Domains0 : Domains 61 State := restrict root0Node60Domains3 3 (3,0)
def root0Node66Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,1),(2,5)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1),(5,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(1,4),(3,4),(5,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node66Domains0_fast_eq : root0Node66Domains0 = expandDomains root0Node66Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node66Domains0 v = expandDomains root0Node66Domains0Fast v from by decide) v
def root0Node66Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(3,0)]
  | 4 => [(2,5)]
  | 5 => [(8,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(5,1),(5,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(7,0)]
  | 50 => [(1,4),(3,4),(5,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5)]
  | 59 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root0Node66Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,5)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1),(5,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(1,4),(3,4),(5,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node66Domains1_fast_eq : root0Node66Domains1 = expandDomains root0Node66Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node66Domains1 v = expandDomains root0Node66Domains1Fast v from by decide) v
theorem root0Node66Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root0Node66Domains0 root0Node66Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node66Domains0 root0Node66Domains1
    root0Node66Domains0Fast root0Node66Domains1Fast
    root0Node66Domains0_fast_eq root0Node66Domains1_fast_eq (by decide)
theorem root0Node66Step1_checked :
    checkReplacement table2 root0Node66Domains0 root0Node66Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node66Step1Chunk0_0_checked, root0Node66Step1Chunk0_1_checked, root0Node66Step1Chunk0_2_checked, root0Node66Step1Chunk0_3_checked, root0Node66Step1Chunk0_4_checked, root0Node66Step1Chunk0_5_checked, root0Node66Step1Chunk1_0_checked, root0Node66Step1Chunk1_1_checked, root0Node66Step1Chunk1_2_checked, root0Node66Step1Chunk1_3_checked, root0Node66Step1Chunk1_4_checked, root0Node66Step1Chunk1_5_checked, root0Node66Step1Chunk2_0_checked, root0Node66Step1Chunk2_1_checked, root0Node66Step1Chunk2_2_checked, root0Node66Step1Chunk2_3_checked, root0Node66Step1Chunk2_4_checked, root0Node66Step1Chunk2_5_checked, root0Node66Step1Chunk3_0_checked, root0Node66Step1Chunk3_1_checked, root0Node66Step1Chunk3_2_checked, root0Node66Step1Chunk3_3_checked, root0Node66Step1Chunk3_4_checked, root0Node66Step1Chunk3_5_checked, root0Node66Step1Chunk4_0_checked, root0Node66Step1Chunk4_1_checked, root0Node66Step1Chunk4_2_checked, root0Node66Step1Chunk4_3_checked, root0Node66Step1Chunk4_4_checked, root0Node66Step1Chunk4_5_checked, root0Node66Step1Chunk5_0_checked, root0Node66Step1Chunk5_1_checked, root0Node66Step1Chunk5_2_checked, root0Node66Step1Chunk5_3_checked, root0Node66Step1Chunk5_4_checked, root0Node66Step1Chunk5_5_checked, root0Node66Step1Chunk6_0_checked, root0Node66Step1Chunk6_1_checked, root0Node66Step1Chunk6_2_checked, root0Node66Step1Chunk6_3_checked, root0Node66Step1Chunk6_4_checked, root0Node66Step1Chunk6_5_checked, root0Node66Step1Chunk7_0_checked, root0Node66Step1Chunk7_1_checked, root0Node66Step1Chunk7_2_checked, root0Node66Step1Chunk7_3_checked, root0Node66Step1Chunk7_4_checked, root0Node66Step1Chunk7_5_checked, root0Node66Step1Chunk8_0_checked, root0Node66Step1Chunk8_1_checked, root0Node66Step1Chunk8_2_checked, root0Node66Step1Chunk8_3_checked, root0Node66Step1Chunk8_4_checked, root0Node66Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node67Domains0 : Domains 61 State := restrict root0Node66Domains1 18 (4,0)
def root0Node67Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,5)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1),(5,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(1,4),(3,4),(5,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node67Domains0_fast_eq : root0Node67Domains0 = expandDomains root0Node67Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node67Domains0 v = expandDomains root0Node67Domains0Fast v from by decide) v
def root0Node67Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(3,0)]
  | 4 => [(2,5)]
  | 5 => [(8,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(8,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(7,0)]
  | 50 => [(5,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root0Node67Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,5)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(8,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(5,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node67Domains1_fast_eq : root0Node67Domains1 = expandDomains root0Node67Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node67Domains1 v = expandDomains root0Node67Domains1Fast v from by decide) v
theorem root0Node67Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node67Domains0 root0Node67Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains0 root0Node67Domains1
    root0Node67Domains0Fast root0Node67Domains1Fast
    root0Node67Domains0_fast_eq root0Node67Domains1_fast_eq (by decide)
theorem root0Node67Step1_checked :
    checkReplacement table37 root0Node67Domains0 root0Node67Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node67Step1Chunk0_0_checked, root0Node67Step1Chunk0_1_checked, root0Node67Step1Chunk0_2_checked, root0Node67Step1Chunk0_3_checked, root0Node67Step1Chunk0_4_checked, root0Node67Step1Chunk0_5_checked, root0Node67Step1Chunk1_0_checked, root0Node67Step1Chunk1_1_checked, root0Node67Step1Chunk1_2_checked, root0Node67Step1Chunk1_3_checked, root0Node67Step1Chunk1_4_checked, root0Node67Step1Chunk1_5_checked, root0Node67Step1Chunk2_0_checked, root0Node67Step1Chunk2_1_checked, root0Node67Step1Chunk2_2_checked, root0Node67Step1Chunk2_3_checked, root0Node67Step1Chunk2_4_checked, root0Node67Step1Chunk2_5_checked, root0Node67Step1Chunk3_0_checked, root0Node67Step1Chunk3_1_checked, root0Node67Step1Chunk3_2_checked, root0Node67Step1Chunk3_3_checked, root0Node67Step1Chunk3_4_checked, root0Node67Step1Chunk3_5_checked, root0Node67Step1Chunk4_0_checked, root0Node67Step1Chunk4_1_checked, root0Node67Step1Chunk4_2_checked, root0Node67Step1Chunk4_3_checked, root0Node67Step1Chunk4_4_checked, root0Node67Step1Chunk4_5_checked, root0Node67Step1Chunk5_0_checked, root0Node67Step1Chunk5_1_checked, root0Node67Step1Chunk5_2_checked, root0Node67Step1Chunk5_3_checked, root0Node67Step1Chunk5_4_checked, root0Node67Step1Chunk5_5_checked, root0Node67Step1Chunk6_0_checked, root0Node67Step1Chunk6_1_checked, root0Node67Step1Chunk6_2_checked, root0Node67Step1Chunk6_3_checked, root0Node67Step1Chunk6_4_checked, root0Node67Step1Chunk6_5_checked, root0Node67Step1Chunk7_0_checked, root0Node67Step1Chunk7_1_checked, root0Node67Step1Chunk7_2_checked, root0Node67Step1Chunk7_3_checked, root0Node67Step1Chunk7_4_checked, root0Node67Step1Chunk7_5_checked, root0Node67Step1Chunk8_0_checked, root0Node67Step1Chunk8_1_checked, root0Node67Step1Chunk8_2_checked, root0Node67Step1Chunk8_3_checked, root0Node67Step1Chunk8_4_checked, root0Node67Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node67Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(3,0)]
  | 4 => [(2,5)]
  | 5 => [(8,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(8,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(7,0)]
  | 50 => [(5,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2)]
  | _ => [(1,1)]
def root0Node67Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,5)]
  | 5 => some [(8,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(8,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(5,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2)]
  | _ => some [(1,1)]
theorem root0Node67Domains2_fast_eq : root0Node67Domains2 = expandDomains root0Node67Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node67Domains2 v = expandDomains root0Node67Domains2Fast v from by decide) v
theorem root0Node67Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node67Domains1 root0Node67Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node67Domains1 root0Node67Domains2
    root0Node67Domains1Fast root0Node67Domains2Fast
    root0Node67Domains1_fast_eq root0Node67Domains2_fast_eq (by decide)
theorem root0Node67Step2_checked :
    checkReplacement table39 root0Node67Domains1 root0Node67Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node67Step2Chunk0_0_checked, root0Node67Step2Chunk0_1_checked, root0Node67Step2Chunk0_2_checked, root0Node67Step2Chunk0_3_checked, root0Node67Step2Chunk0_4_checked, root0Node67Step2Chunk0_5_checked, root0Node67Step2Chunk1_0_checked, root0Node67Step2Chunk1_1_checked, root0Node67Step2Chunk1_2_checked, root0Node67Step2Chunk1_3_checked, root0Node67Step2Chunk1_4_checked, root0Node67Step2Chunk1_5_checked, root0Node67Step2Chunk2_0_checked, root0Node67Step2Chunk2_1_checked, root0Node67Step2Chunk2_2_checked, root0Node67Step2Chunk2_3_checked, root0Node67Step2Chunk2_4_checked, root0Node67Step2Chunk2_5_checked, root0Node67Step2Chunk3_0_checked, root0Node67Step2Chunk3_1_checked, root0Node67Step2Chunk3_2_checked, root0Node67Step2Chunk3_3_checked, root0Node67Step2Chunk3_4_checked, root0Node67Step2Chunk3_5_checked, root0Node67Step2Chunk4_0_checked, root0Node67Step2Chunk4_1_checked, root0Node67Step2Chunk4_2_checked, root0Node67Step2Chunk4_3_checked, root0Node67Step2Chunk4_4_checked, root0Node67Step2Chunk4_5_checked, root0Node67Step2Chunk5_0_checked, root0Node67Step2Chunk5_1_checked, root0Node67Step2Chunk5_2_checked, root0Node67Step2Chunk5_3_checked, root0Node67Step2Chunk5_4_checked, root0Node67Step2Chunk5_5_checked, root0Node67Step2Chunk6_0_checked, root0Node67Step2Chunk6_1_checked, root0Node67Step2Chunk6_2_checked, root0Node67Step2Chunk6_3_checked, root0Node67Step2Chunk6_4_checked, root0Node67Step2Chunk6_5_checked, root0Node67Step2Chunk7_0_checked, root0Node67Step2Chunk7_1_checked, root0Node67Step2Chunk7_2_checked, root0Node67Step2Chunk7_3_checked, root0Node67Step2Chunk7_4_checked, root0Node67Step2Chunk7_5_checked, root0Node67Step2Chunk8_0_checked, root0Node67Step2Chunk8_1_checked, root0Node67Step2Chunk8_2_checked, root0Node67Step2Chunk8_3_checked, root0Node67Step2Chunk8_4_checked, root0Node67Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node67Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node67Domains2 (.output 33) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
