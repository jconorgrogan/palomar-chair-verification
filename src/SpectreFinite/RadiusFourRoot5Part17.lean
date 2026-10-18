module

public import SpectreFinite.RadiusFourRoot5Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable3
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node52Domains0 : Domains 61 State := restrict root5Node51Domains1 52 (5,5)
def root5Node52Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0)]
  | 10 => some [(2,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node52Domains0_fast_eq : root5Node52Domains0 = expandDomains root5Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node52Domains0 v = expandDomains root5Node52Domains0Fast v from by decide) v
def root5Node52Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(1,4)]
  | _ => [(0,5)]
def root5Node52Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0)]
  | 10 => some [(2,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | _ => some [(0,5)]
theorem root5Node52Domains1_fast_eq : root5Node52Domains1 = expandDomains root5Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node52Domains1 v = expandDomains root5Node52Domains1Fast v from by decide) v
theorem root5Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node52Domains0 root5Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node52Domains0 root5Node52Domains1
    root5Node52Domains0Fast root5Node52Domains1Fast
    root5Node52Domains0_fast_eq root5Node52Domains1_fast_eq (by decide)
theorem root5Node52Step1_checked :
    checkReplacement table46 root5Node52Domains0 root5Node52Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node52Step1Chunk0_0_checked, root5Node52Step1Chunk0_1_checked, root5Node52Step1Chunk0_2_checked, root5Node52Step1Chunk0_3_checked, root5Node52Step1Chunk0_4_checked, root5Node52Step1Chunk0_5_checked, root5Node52Step1Chunk1_0_checked, root5Node52Step1Chunk1_1_checked, root5Node52Step1Chunk1_2_checked, root5Node52Step1Chunk1_3_checked, root5Node52Step1Chunk1_4_checked, root5Node52Step1Chunk1_5_checked, root5Node52Step1Chunk2_0_checked, root5Node52Step1Chunk2_1_checked, root5Node52Step1Chunk2_2_checked, root5Node52Step1Chunk2_3_checked, root5Node52Step1Chunk2_4_checked, root5Node52Step1Chunk2_5_checked, root5Node52Step1Chunk3_0_checked, root5Node52Step1Chunk3_1_checked, root5Node52Step1Chunk3_2_checked, root5Node52Step1Chunk3_3_checked, root5Node52Step1Chunk3_4_checked, root5Node52Step1Chunk3_5_checked, root5Node52Step1Chunk4_0_checked, root5Node52Step1Chunk4_1_checked, root5Node52Step1Chunk4_2_checked, root5Node52Step1Chunk4_3_checked, root5Node52Step1Chunk4_4_checked, root5Node52Step1Chunk4_5_checked, root5Node52Step1Chunk5_0_checked, root5Node52Step1Chunk5_1_checked, root5Node52Step1Chunk5_2_checked, root5Node52Step1Chunk5_3_checked, root5Node52Step1Chunk5_4_checked, root5Node52Step1Chunk5_5_checked, root5Node52Step1Chunk6_0_checked, root5Node52Step1Chunk6_1_checked, root5Node52Step1Chunk6_2_checked, root5Node52Step1Chunk6_3_checked, root5Node52Step1Chunk6_4_checked, root5Node52Step1Chunk6_5_checked, root5Node52Step1Chunk7_0_checked, root5Node52Step1Chunk7_1_checked, root5Node52Step1Chunk7_2_checked, root5Node52Step1Chunk7_3_checked, root5Node52Step1Chunk7_4_checked, root5Node52Step1Chunk7_5_checked, root5Node52Step1Chunk8_0_checked, root5Node52Step1Chunk8_1_checked, root5Node52Step1Chunk8_2_checked, root5Node52Step1Chunk8_3_checked, root5Node52Step1Chunk8_4_checked, root5Node52Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node52Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node52Domains1 (.output 25) = true := by decide
def root5Node53Domains0 : Domains 61 State := restrict root5Node51Domains1 52 (8,5)
def root5Node53Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0)]
  | 10 => some [(2,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node53Domains0_fast_eq : root5Node53Domains0 = expandDomains root5Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node53Domains0 v = expandDomains root5Node53Domains0Fast v from by decide) v
def root5Node53Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0)]
  | 10 => [(2,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(3,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root5Node53Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0)]
  | 10 => some [(2,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(3,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node53Domains1_fast_eq : root5Node53Domains1 = expandDomains root5Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node53Domains1 v = expandDomains root5Node53Domains1Fast v from by decide) v
theorem root5Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node53Domains0 root5Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node53Domains0 root5Node53Domains1
    root5Node53Domains0Fast root5Node53Domains1Fast
    root5Node53Domains0_fast_eq root5Node53Domains1_fast_eq (by decide)
theorem root5Node53Step1_checked :
    checkReplacement table46 root5Node53Domains0 root5Node53Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node53Step1Chunk0_0_checked, root5Node53Step1Chunk0_1_checked, root5Node53Step1Chunk0_2_checked, root5Node53Step1Chunk0_3_checked, root5Node53Step1Chunk0_4_checked, root5Node53Step1Chunk0_5_checked, root5Node53Step1Chunk1_0_checked, root5Node53Step1Chunk1_1_checked, root5Node53Step1Chunk1_2_checked, root5Node53Step1Chunk1_3_checked, root5Node53Step1Chunk1_4_checked, root5Node53Step1Chunk1_5_checked, root5Node53Step1Chunk2_0_checked, root5Node53Step1Chunk2_1_checked, root5Node53Step1Chunk2_2_checked, root5Node53Step1Chunk2_3_checked, root5Node53Step1Chunk2_4_checked, root5Node53Step1Chunk2_5_checked, root5Node53Step1Chunk3_0_checked, root5Node53Step1Chunk3_1_checked, root5Node53Step1Chunk3_2_checked, root5Node53Step1Chunk3_3_checked, root5Node53Step1Chunk3_4_checked, root5Node53Step1Chunk3_5_checked, root5Node53Step1Chunk4_0_checked, root5Node53Step1Chunk4_1_checked, root5Node53Step1Chunk4_2_checked, root5Node53Step1Chunk4_3_checked, root5Node53Step1Chunk4_4_checked, root5Node53Step1Chunk4_5_checked, root5Node53Step1Chunk5_0_checked, root5Node53Step1Chunk5_1_checked, root5Node53Step1Chunk5_2_checked, root5Node53Step1Chunk5_3_checked, root5Node53Step1Chunk5_4_checked, root5Node53Step1Chunk5_5_checked, root5Node53Step1Chunk6_0_checked, root5Node53Step1Chunk6_1_checked, root5Node53Step1Chunk6_2_checked, root5Node53Step1Chunk6_3_checked, root5Node53Step1Chunk6_4_checked, root5Node53Step1Chunk6_5_checked, root5Node53Step1Chunk7_0_checked, root5Node53Step1Chunk7_1_checked, root5Node53Step1Chunk7_2_checked, root5Node53Step1Chunk7_3_checked, root5Node53Step1Chunk7_4_checked, root5Node53Step1Chunk7_5_checked, root5Node53Step1Chunk8_0_checked, root5Node53Step1Chunk8_1_checked, root5Node53Step1Chunk8_2_checked, root5Node53Step1Chunk8_3_checked, root5Node53Step1Chunk8_4_checked, root5Node53Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node53Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node53Domains1 (.output 26) = true := by decide
def root5Node54Domains0 : Domains 61 State := restrict root5Node48Domains3 2 (8,1)
def root5Node54Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0),(3,0)]
  | 10 => some [(2,1),(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1),(5,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node54Domains0_fast_eq : root5Node54Domains0 = expandDomains root5Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node54Domains0 v = expandDomains root5Node54Domains0Fast v from by decide) v
def root5Node54Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1),(5,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(5,0),(5,3)]
  | 52 => [(4,5),(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4)]
  | 57 => [(0,0),(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node54Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1),(5,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node54Domains1_fast_eq : root5Node54Domains1 = expandDomains root5Node54Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node54Domains1 v = expandDomains root5Node54Domains1Fast v from by decide) v
theorem root5Node54Step1Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root5Node54Domains0 root5Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node54Domains0 root5Node54Domains1
    root5Node54Domains0Fast root5Node54Domains1Fast
    root5Node54Domains0_fast_eq root5Node54Domains1_fast_eq (by decide)
theorem root5Node54Step1_checked :
    checkReplacement table3 root5Node54Domains0 root5Node54Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node54Step1Chunk0_0_checked, root5Node54Step1Chunk0_1_checked, root5Node54Step1Chunk0_2_checked, root5Node54Step1Chunk0_3_checked, root5Node54Step1Chunk0_4_checked, root5Node54Step1Chunk0_5_checked, root5Node54Step1Chunk1_0_checked, root5Node54Step1Chunk1_1_checked, root5Node54Step1Chunk1_2_checked, root5Node54Step1Chunk1_3_checked, root5Node54Step1Chunk1_4_checked, root5Node54Step1Chunk1_5_checked, root5Node54Step1Chunk2_0_checked, root5Node54Step1Chunk2_1_checked, root5Node54Step1Chunk2_2_checked, root5Node54Step1Chunk2_3_checked, root5Node54Step1Chunk2_4_checked, root5Node54Step1Chunk2_5_checked, root5Node54Step1Chunk3_0_checked, root5Node54Step1Chunk3_1_checked, root5Node54Step1Chunk3_2_checked, root5Node54Step1Chunk3_3_checked, root5Node54Step1Chunk3_4_checked, root5Node54Step1Chunk3_5_checked, root5Node54Step1Chunk4_0_checked, root5Node54Step1Chunk4_1_checked, root5Node54Step1Chunk4_2_checked, root5Node54Step1Chunk4_3_checked, root5Node54Step1Chunk4_4_checked, root5Node54Step1Chunk4_5_checked, root5Node54Step1Chunk5_0_checked, root5Node54Step1Chunk5_1_checked, root5Node54Step1Chunk5_2_checked, root5Node54Step1Chunk5_3_checked, root5Node54Step1Chunk5_4_checked, root5Node54Step1Chunk5_5_checked, root5Node54Step1Chunk6_0_checked, root5Node54Step1Chunk6_1_checked, root5Node54Step1Chunk6_2_checked, root5Node54Step1Chunk6_3_checked, root5Node54Step1Chunk6_4_checked, root5Node54Step1Chunk6_5_checked, root5Node54Step1Chunk7_0_checked, root5Node54Step1Chunk7_1_checked, root5Node54Step1Chunk7_2_checked, root5Node54Step1Chunk7_3_checked, root5Node54Step1Chunk7_4_checked, root5Node54Step1Chunk7_5_checked, root5Node54Step1Chunk8_0_checked, root5Node54Step1Chunk8_1_checked, root5Node54Step1Chunk8_2_checked, root5Node54Step1Chunk8_3_checked, root5Node54Step1Chunk8_4_checked, root5Node54Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node55Domains0 : Domains 61 State := restrict root5Node54Domains1 26 (7,2)
def root5Node55Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1),(5,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node55Domains0_fast_eq : root5Node55Domains0 = expandDomains root5Node55Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node55Domains0 v = expandDomains root5Node55Domains0Fast v from by decide) v
def root5Node55Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(5,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node55Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node55Domains1_fast_eq : root5Node55Domains1 = expandDomains root5Node55Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node55Domains1 v = expandDomains root5Node55Domains1Fast v from by decide) v
theorem root5Node55Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root5Node55Domains0 root5Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains0 root5Node55Domains1
    root5Node55Domains0Fast root5Node55Domains1Fast
    root5Node55Domains0_fast_eq root5Node55Domains1_fast_eq (by decide)
theorem root5Node55Step1_checked :
    checkReplacement table37 root5Node55Domains0 root5Node55Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node55Step1Chunk0_0_checked, root5Node55Step1Chunk0_1_checked, root5Node55Step1Chunk0_2_checked, root5Node55Step1Chunk0_3_checked, root5Node55Step1Chunk0_4_checked, root5Node55Step1Chunk0_5_checked, root5Node55Step1Chunk1_0_checked, root5Node55Step1Chunk1_1_checked, root5Node55Step1Chunk1_2_checked, root5Node55Step1Chunk1_3_checked, root5Node55Step1Chunk1_4_checked, root5Node55Step1Chunk1_5_checked, root5Node55Step1Chunk2_0_checked, root5Node55Step1Chunk2_1_checked, root5Node55Step1Chunk2_2_checked, root5Node55Step1Chunk2_3_checked, root5Node55Step1Chunk2_4_checked, root5Node55Step1Chunk2_5_checked, root5Node55Step1Chunk3_0_checked, root5Node55Step1Chunk3_1_checked, root5Node55Step1Chunk3_2_checked, root5Node55Step1Chunk3_3_checked, root5Node55Step1Chunk3_4_checked, root5Node55Step1Chunk3_5_checked, root5Node55Step1Chunk4_0_checked, root5Node55Step1Chunk4_1_checked, root5Node55Step1Chunk4_2_checked, root5Node55Step1Chunk4_3_checked, root5Node55Step1Chunk4_4_checked, root5Node55Step1Chunk4_5_checked, root5Node55Step1Chunk5_0_checked, root5Node55Step1Chunk5_1_checked, root5Node55Step1Chunk5_2_checked, root5Node55Step1Chunk5_3_checked, root5Node55Step1Chunk5_4_checked, root5Node55Step1Chunk5_5_checked, root5Node55Step1Chunk6_0_checked, root5Node55Step1Chunk6_1_checked, root5Node55Step1Chunk6_2_checked, root5Node55Step1Chunk6_3_checked, root5Node55Step1Chunk6_4_checked, root5Node55Step1Chunk6_5_checked, root5Node55Step1Chunk7_0_checked, root5Node55Step1Chunk7_1_checked, root5Node55Step1Chunk7_2_checked, root5Node55Step1Chunk7_3_checked, root5Node55Step1Chunk7_4_checked, root5Node55Step1Chunk7_5_checked, root5Node55Step1Chunk8_0_checked, root5Node55Step1Chunk8_1_checked, root5Node55Step1Chunk8_2_checked, root5Node55Step1Chunk8_3_checked, root5Node55Step1Chunk8_4_checked, root5Node55Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node55Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root5Node55Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node55Domains2_fast_eq : root5Node55Domains2 = expandDomains root5Node55Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node55Domains2 v = expandDomains root5Node55Domains2Fast v from by decide) v
theorem root5Node55Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root5Node55Domains1 root5Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node55Domains1 root5Node55Domains2
    root5Node55Domains1Fast root5Node55Domains2Fast
    root5Node55Domains1_fast_eq root5Node55Domains2_fast_eq (by decide)
theorem root5Node55Step2_checked :
    checkReplacement table39 root5Node55Domains1 root5Node55Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node55Step2Chunk0_0_checked, root5Node55Step2Chunk0_1_checked, root5Node55Step2Chunk0_2_checked, root5Node55Step2Chunk0_3_checked, root5Node55Step2Chunk0_4_checked, root5Node55Step2Chunk0_5_checked, root5Node55Step2Chunk1_0_checked, root5Node55Step2Chunk1_1_checked, root5Node55Step2Chunk1_2_checked, root5Node55Step2Chunk1_3_checked, root5Node55Step2Chunk1_4_checked, root5Node55Step2Chunk1_5_checked, root5Node55Step2Chunk2_0_checked, root5Node55Step2Chunk2_1_checked, root5Node55Step2Chunk2_2_checked, root5Node55Step2Chunk2_3_checked, root5Node55Step2Chunk2_4_checked, root5Node55Step2Chunk2_5_checked, root5Node55Step2Chunk3_0_checked, root5Node55Step2Chunk3_1_checked, root5Node55Step2Chunk3_2_checked, root5Node55Step2Chunk3_3_checked, root5Node55Step2Chunk3_4_checked, root5Node55Step2Chunk3_5_checked, root5Node55Step2Chunk4_0_checked, root5Node55Step2Chunk4_1_checked, root5Node55Step2Chunk4_2_checked, root5Node55Step2Chunk4_3_checked, root5Node55Step2Chunk4_4_checked, root5Node55Step2Chunk4_5_checked, root5Node55Step2Chunk5_0_checked, root5Node55Step2Chunk5_1_checked, root5Node55Step2Chunk5_2_checked, root5Node55Step2Chunk5_3_checked, root5Node55Step2Chunk5_4_checked, root5Node55Step2Chunk5_5_checked, root5Node55Step2Chunk6_0_checked, root5Node55Step2Chunk6_1_checked, root5Node55Step2Chunk6_2_checked, root5Node55Step2Chunk6_3_checked, root5Node55Step2Chunk6_4_checked, root5Node55Step2Chunk6_5_checked, root5Node55Step2Chunk7_0_checked, root5Node55Step2Chunk7_1_checked, root5Node55Step2Chunk7_2_checked, root5Node55Step2Chunk7_3_checked, root5Node55Step2Chunk7_4_checked, root5Node55Step2Chunk7_5_checked, root5Node55Step2Chunk8_0_checked, root5Node55Step2Chunk8_1_checked, root5Node55Step2Chunk8_2_checked, root5Node55Step2Chunk8_3_checked, root5Node55Step2Chunk8_4_checked, root5Node55Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node55Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node55Domains2 (.output 27) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
