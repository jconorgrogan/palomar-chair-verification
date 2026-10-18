module

public import SpectreFinite.RadiusFourRoot8Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable18
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable40
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node12Domains0 : Domains 61 State := restrict root8Node10Domains1 33 (7,0)
def root8Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(2,3),(2,5)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root8Node12Domains0_fast_eq : root8Node12Domains0 = expandDomains root8Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node12Domains0 v = expandDomains root8Node12Domains0Fast v from by decide) v
def root8Node12Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(0,5)]
  | 27 => [(2,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(7,0)]
  | 34 => [(2,3)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(6,4)]
  | 43 => [(4,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(6,4)]
def root8Node12Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(2,3)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(6,4)]
theorem root8Node12Domains1_fast_eq : root8Node12Domains1 = expandDomains root8Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node12Domains1 v = expandDomains root8Node12Domains1Fast v from by decide) v
theorem root8Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1_checked :
    checkReplacement table40 root8Node12Domains0 root8Node12Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node12Step1Chunk0_0_checked, root8Node12Step1Chunk0_1_checked, root8Node12Step1Chunk0_2_checked, root8Node12Step1Chunk0_3_checked, root8Node12Step1Chunk0_4_checked, root8Node12Step1Chunk0_5_checked, root8Node12Step1Chunk1_0_checked, root8Node12Step1Chunk1_1_checked, root8Node12Step1Chunk1_2_checked, root8Node12Step1Chunk1_3_checked, root8Node12Step1Chunk1_4_checked, root8Node12Step1Chunk1_5_checked, root8Node12Step1Chunk2_0_checked, root8Node12Step1Chunk2_1_checked, root8Node12Step1Chunk2_2_checked, root8Node12Step1Chunk2_3_checked, root8Node12Step1Chunk2_4_checked, root8Node12Step1Chunk2_5_checked, root8Node12Step1Chunk3_0_checked, root8Node12Step1Chunk3_1_checked, root8Node12Step1Chunk3_2_checked, root8Node12Step1Chunk3_3_checked, root8Node12Step1Chunk3_4_checked, root8Node12Step1Chunk3_5_checked, root8Node12Step1Chunk4_0_checked, root8Node12Step1Chunk4_1_checked, root8Node12Step1Chunk4_2_checked, root8Node12Step1Chunk4_3_checked, root8Node12Step1Chunk4_4_checked, root8Node12Step1Chunk4_5_checked, root8Node12Step1Chunk5_0_checked, root8Node12Step1Chunk5_1_checked, root8Node12Step1Chunk5_2_checked, root8Node12Step1Chunk5_3_checked, root8Node12Step1Chunk5_4_checked, root8Node12Step1Chunk5_5_checked, root8Node12Step1Chunk6_0_checked, root8Node12Step1Chunk6_1_checked, root8Node12Step1Chunk6_2_checked, root8Node12Step1Chunk6_3_checked, root8Node12Step1Chunk6_4_checked, root8Node12Step1Chunk6_5_checked, root8Node12Step1Chunk7_0_checked, root8Node12Step1Chunk7_1_checked, root8Node12Step1Chunk7_2_checked, root8Node12Step1Chunk7_3_checked, root8Node12Step1Chunk7_4_checked, root8Node12Step1Chunk7_5_checked, root8Node12Step1Chunk8_0_checked, root8Node12Step1Chunk8_1_checked, root8Node12Step1Chunk8_2_checked, root8Node12Step1Chunk8_3_checked, root8Node12Step1Chunk8_4_checked, root8Node12Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node12Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node12Domains1 (.output 4) = true := by decide
def root8Node13Domains0 : Domains 61 State := restrict root8Node9Domains2 17 (6,3)
def root8Node13Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(2,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,5)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node13Domains0_fast_eq : root8Node13Domains0 = expandDomains root8Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node13Domains0 v = expandDomains root8Node13Domains0Fast v from by decide) v
def root8Node13Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(2,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5)]
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
def root8Node13Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(2,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5)]
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
theorem root8Node13Domains1_fast_eq : root8Node13Domains1 = expandDomains root8Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node13Domains1 v = expandDomains root8Node13Domains1Fast v from by decide) v
theorem root8Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1_checked :
    checkReplacement table40 root8Node13Domains0 root8Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node13Step1Chunk0_0_checked, root8Node13Step1Chunk0_1_checked, root8Node13Step1Chunk0_2_checked, root8Node13Step1Chunk0_3_checked, root8Node13Step1Chunk0_4_checked, root8Node13Step1Chunk0_5_checked, root8Node13Step1Chunk1_0_checked, root8Node13Step1Chunk1_1_checked, root8Node13Step1Chunk1_2_checked, root8Node13Step1Chunk1_3_checked, root8Node13Step1Chunk1_4_checked, root8Node13Step1Chunk1_5_checked, root8Node13Step1Chunk2_0_checked, root8Node13Step1Chunk2_1_checked, root8Node13Step1Chunk2_2_checked, root8Node13Step1Chunk2_3_checked, root8Node13Step1Chunk2_4_checked, root8Node13Step1Chunk2_5_checked, root8Node13Step1Chunk3_0_checked, root8Node13Step1Chunk3_1_checked, root8Node13Step1Chunk3_2_checked, root8Node13Step1Chunk3_3_checked, root8Node13Step1Chunk3_4_checked, root8Node13Step1Chunk3_5_checked, root8Node13Step1Chunk4_0_checked, root8Node13Step1Chunk4_1_checked, root8Node13Step1Chunk4_2_checked, root8Node13Step1Chunk4_3_checked, root8Node13Step1Chunk4_4_checked, root8Node13Step1Chunk4_5_checked, root8Node13Step1Chunk5_0_checked, root8Node13Step1Chunk5_1_checked, root8Node13Step1Chunk5_2_checked, root8Node13Step1Chunk5_3_checked, root8Node13Step1Chunk5_4_checked, root8Node13Step1Chunk5_5_checked, root8Node13Step1Chunk6_0_checked, root8Node13Step1Chunk6_1_checked, root8Node13Step1Chunk6_2_checked, root8Node13Step1Chunk6_3_checked, root8Node13Step1Chunk6_4_checked, root8Node13Step1Chunk6_5_checked, root8Node13Step1Chunk7_0_checked, root8Node13Step1Chunk7_1_checked, root8Node13Step1Chunk7_2_checked, root8Node13Step1Chunk7_3_checked, root8Node13Step1Chunk7_4_checked, root8Node13Step1Chunk7_5_checked, root8Node13Step1Chunk8_0_checked, root8Node13Step1Chunk8_1_checked, root8Node13Step1Chunk8_2_checked, root8Node13Step1Chunk8_3_checked, root8Node13Step1Chunk8_4_checked, root8Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node13Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node13Domains1 (.output 5) = true := by decide
def root8Node14Domains0 : Domains 61 State := restrict root8Node8Domains1 5 (8,5)
def root8Node14Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3),(6,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,5)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node14Domains0_fast_eq : root8Node14Domains0 = expandDomains root8Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node14Domains0 v = expandDomains root8Node14Domains0Fast v from by decide) v
def root8Node14Domains1 (v : Fin 61) : List State :=
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
  | 17 => [(1,3),(6,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(8,1)]
  | 24 => [(0,2),(6,5)]
  | 25 => [(0,4),(1,1)]
  | 26 => [(1,2),(3,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(3,0),(5,0),(7,0)]
  | 34 => [(2,3),(2,5),(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3),(6,4)]
def root8Node14Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 17 => some [(1,3),(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(1,2),(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node14Domains1_fast_eq : root8Node14Domains1 = expandDomains root8Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node14Domains1 v = expandDomains root8Node14Domains1Fast v from by decide) v
theorem root8Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1_checked :
    checkReplacement table18 root8Node14Domains0 root8Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node14Step1Chunk0_0_checked, root8Node14Step1Chunk0_1_checked, root8Node14Step1Chunk0_2_checked, root8Node14Step1Chunk0_3_checked, root8Node14Step1Chunk0_4_checked, root8Node14Step1Chunk0_5_checked, root8Node14Step1Chunk1_0_checked, root8Node14Step1Chunk1_1_checked, root8Node14Step1Chunk1_2_checked, root8Node14Step1Chunk1_3_checked, root8Node14Step1Chunk1_4_checked, root8Node14Step1Chunk1_5_checked, root8Node14Step1Chunk2_0_checked, root8Node14Step1Chunk2_1_checked, root8Node14Step1Chunk2_2_checked, root8Node14Step1Chunk2_3_checked, root8Node14Step1Chunk2_4_checked, root8Node14Step1Chunk2_5_checked, root8Node14Step1Chunk3_0_checked, root8Node14Step1Chunk3_1_checked, root8Node14Step1Chunk3_2_checked, root8Node14Step1Chunk3_3_checked, root8Node14Step1Chunk3_4_checked, root8Node14Step1Chunk3_5_checked, root8Node14Step1Chunk4_0_checked, root8Node14Step1Chunk4_1_checked, root8Node14Step1Chunk4_2_checked, root8Node14Step1Chunk4_3_checked, root8Node14Step1Chunk4_4_checked, root8Node14Step1Chunk4_5_checked, root8Node14Step1Chunk5_0_checked, root8Node14Step1Chunk5_1_checked, root8Node14Step1Chunk5_2_checked, root8Node14Step1Chunk5_3_checked, root8Node14Step1Chunk5_4_checked, root8Node14Step1Chunk5_5_checked, root8Node14Step1Chunk6_0_checked, root8Node14Step1Chunk6_1_checked, root8Node14Step1Chunk6_2_checked, root8Node14Step1Chunk6_3_checked, root8Node14Step1Chunk6_4_checked, root8Node14Step1Chunk6_5_checked, root8Node14Step1Chunk7_0_checked, root8Node14Step1Chunk7_1_checked, root8Node14Step1Chunk7_2_checked, root8Node14Step1Chunk7_3_checked, root8Node14Step1Chunk7_4_checked, root8Node14Step1Chunk7_5_checked, root8Node14Step1Chunk8_0_checked, root8Node14Step1Chunk8_1_checked, root8Node14Step1Chunk8_2_checked, root8Node14Step1Chunk8_3_checked, root8Node14Step1Chunk8_4_checked, root8Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node14Domains2 (v : Fin 61) : List State :=
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
  | 17 => [(1,3),(6,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(8,1)]
  | 24 => [(0,2),(6,5)]
  | 25 => [(0,4),(1,1)]
  | 26 => [(1,2),(3,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(3,0),(5,0),(7,0)]
  | 34 => [(2,3),(2,5),(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3)]
  | 55 => [(4,5),(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3)]
def root8Node14Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 17 => some [(1,3),(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(1,2),(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3)]
  | 55 => some [(4,5),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3)]
theorem root8Node14Domains2_fast_eq : root8Node14Domains2 = expandDomains root8Node14Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node14Domains2 v = expandDomains root8Node14Domains2Fast v from by decide) v
theorem root8Node14Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root8Node14Domains1 root8Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains1 root8Node14Domains2
    root8Node14Domains1Fast root8Node14Domains2Fast
    root8Node14Domains1_fast_eq root8Node14Domains2_fast_eq (by decide)
theorem root8Node14Step2_checked :
    checkReplacement table46 root8Node14Domains1 root8Node14Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node14Step2Chunk0_0_checked, root8Node14Step2Chunk0_1_checked, root8Node14Step2Chunk0_2_checked, root8Node14Step2Chunk0_3_checked, root8Node14Step2Chunk0_4_checked, root8Node14Step2Chunk0_5_checked, root8Node14Step2Chunk1_0_checked, root8Node14Step2Chunk1_1_checked, root8Node14Step2Chunk1_2_checked, root8Node14Step2Chunk1_3_checked, root8Node14Step2Chunk1_4_checked, root8Node14Step2Chunk1_5_checked, root8Node14Step2Chunk2_0_checked, root8Node14Step2Chunk2_1_checked, root8Node14Step2Chunk2_2_checked, root8Node14Step2Chunk2_3_checked, root8Node14Step2Chunk2_4_checked, root8Node14Step2Chunk2_5_checked, root8Node14Step2Chunk3_0_checked, root8Node14Step2Chunk3_1_checked, root8Node14Step2Chunk3_2_checked, root8Node14Step2Chunk3_3_checked, root8Node14Step2Chunk3_4_checked, root8Node14Step2Chunk3_5_checked, root8Node14Step2Chunk4_0_checked, root8Node14Step2Chunk4_1_checked, root8Node14Step2Chunk4_2_checked, root8Node14Step2Chunk4_3_checked, root8Node14Step2Chunk4_4_checked, root8Node14Step2Chunk4_5_checked, root8Node14Step2Chunk5_0_checked, root8Node14Step2Chunk5_1_checked, root8Node14Step2Chunk5_2_checked, root8Node14Step2Chunk5_3_checked, root8Node14Step2Chunk5_4_checked, root8Node14Step2Chunk5_5_checked, root8Node14Step2Chunk6_0_checked, root8Node14Step2Chunk6_1_checked, root8Node14Step2Chunk6_2_checked, root8Node14Step2Chunk6_3_checked, root8Node14Step2Chunk6_4_checked, root8Node14Step2Chunk6_5_checked, root8Node14Step2Chunk7_0_checked, root8Node14Step2Chunk7_1_checked, root8Node14Step2Chunk7_2_checked, root8Node14Step2Chunk7_3_checked, root8Node14Step2Chunk7_4_checked, root8Node14Step2Chunk7_5_checked, root8Node14Step2Chunk8_0_checked, root8Node14Step2Chunk8_1_checked, root8Node14Step2Chunk8_2_checked, root8Node14Step2Chunk8_3_checked, root8Node14Step2Chunk8_4_checked, root8Node14Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node14Domains3 (v : Fin 61) : List State :=
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
  | 17 => [(1,3),(6,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(8,1)]
  | 24 => [(0,2),(6,5)]
  | 25 => [(0,4),(1,1)]
  | 26 => [(1,2),(3,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(3,0),(5,0)]
  | 34 => [(2,5),(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3)]
  | 55 => [(4,5),(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3)]
def root8Node14Domains3Fast (v : Fin 61) : Option (List State) :=
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
  | 17 => some [(1,3),(6,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(1,2),(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0)]
  | 34 => some [(2,5),(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3)]
  | 55 => some [(4,5),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3)]
theorem root8Node14Domains3_fast_eq : root8Node14Domains3 = expandDomains root8Node14Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node14Domains3 v = expandDomains root8Node14Domains3Fast v from by decide) v
theorem root8Node14Step3Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node14Domains2 root8Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains2 root8Node14Domains3
    root8Node14Domains2Fast root8Node14Domains3Fast
    root8Node14Domains2_fast_eq root8Node14Domains3_fast_eq (by decide)
theorem root8Node14Step3_checked :
    checkReplacement table23 root8Node14Domains2 root8Node14Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node14Step3Chunk0_0_checked, root8Node14Step3Chunk0_1_checked, root8Node14Step3Chunk0_2_checked, root8Node14Step3Chunk0_3_checked, root8Node14Step3Chunk0_4_checked, root8Node14Step3Chunk0_5_checked, root8Node14Step3Chunk1_0_checked, root8Node14Step3Chunk1_1_checked, root8Node14Step3Chunk1_2_checked, root8Node14Step3Chunk1_3_checked, root8Node14Step3Chunk1_4_checked, root8Node14Step3Chunk1_5_checked, root8Node14Step3Chunk2_0_checked, root8Node14Step3Chunk2_1_checked, root8Node14Step3Chunk2_2_checked, root8Node14Step3Chunk2_3_checked, root8Node14Step3Chunk2_4_checked, root8Node14Step3Chunk2_5_checked, root8Node14Step3Chunk3_0_checked, root8Node14Step3Chunk3_1_checked, root8Node14Step3Chunk3_2_checked, root8Node14Step3Chunk3_3_checked, root8Node14Step3Chunk3_4_checked, root8Node14Step3Chunk3_5_checked, root8Node14Step3Chunk4_0_checked, root8Node14Step3Chunk4_1_checked, root8Node14Step3Chunk4_2_checked, root8Node14Step3Chunk4_3_checked, root8Node14Step3Chunk4_4_checked, root8Node14Step3Chunk4_5_checked, root8Node14Step3Chunk5_0_checked, root8Node14Step3Chunk5_1_checked, root8Node14Step3Chunk5_2_checked, root8Node14Step3Chunk5_3_checked, root8Node14Step3Chunk5_4_checked, root8Node14Step3Chunk5_5_checked, root8Node14Step3Chunk6_0_checked, root8Node14Step3Chunk6_1_checked, root8Node14Step3Chunk6_2_checked, root8Node14Step3Chunk6_3_checked, root8Node14Step3Chunk6_4_checked, root8Node14Step3Chunk6_5_checked, root8Node14Step3Chunk7_0_checked, root8Node14Step3Chunk7_1_checked, root8Node14Step3Chunk7_2_checked, root8Node14Step3Chunk7_3_checked, root8Node14Step3Chunk7_4_checked, root8Node14Step3Chunk7_5_checked, root8Node14Step3Chunk8_0_checked, root8Node14Step3Chunk8_1_checked, root8Node14Step3Chunk8_2_checked, root8Node14Step3Chunk8_3_checked, root8Node14Step3Chunk8_4_checked, root8Node14Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
