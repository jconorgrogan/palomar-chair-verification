module

public import SpectreFinite.RadiusFourRoot7Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node53Domains0 : Domains 61 State := restrict root7Node52Domains1 34 (2,3)
def root7Node53Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(2,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(2,5)]
  | 44 => some [(6,0)]
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
theorem root7Node53Domains0_fast_eq : root7Node53Domains0 = expandDomains root7Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node53Domains0 v = expandDomains root7Node53Domains0Fast v from by decide) v
def root7Node53Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(7,0)]
  | 34 => [(2,3)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(6,4)]
  | 43 => [(2,5)]
  | 44 => [(6,0)]
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
def root7Node53Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(2,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(6,4)]
  | 43 => some [(2,5)]
  | 44 => some [(6,0)]
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
theorem root7Node53Domains1_fast_eq : root7Node53Domains1 = expandDomains root7Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node53Domains1 v = expandDomains root7Node53Domains1Fast v from by decide) v
theorem root7Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1_checked :
    checkReplacement table16 root7Node53Domains0 root7Node53Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node53Step1Chunk0_0_checked, root7Node53Step1Chunk0_1_checked, root7Node53Step1Chunk0_2_checked, root7Node53Step1Chunk0_3_checked, root7Node53Step1Chunk0_4_checked, root7Node53Step1Chunk0_5_checked, root7Node53Step1Chunk1_0_checked, root7Node53Step1Chunk1_1_checked, root7Node53Step1Chunk1_2_checked, root7Node53Step1Chunk1_3_checked, root7Node53Step1Chunk1_4_checked, root7Node53Step1Chunk1_5_checked, root7Node53Step1Chunk2_0_checked, root7Node53Step1Chunk2_1_checked, root7Node53Step1Chunk2_2_checked, root7Node53Step1Chunk2_3_checked, root7Node53Step1Chunk2_4_checked, root7Node53Step1Chunk2_5_checked, root7Node53Step1Chunk3_0_checked, root7Node53Step1Chunk3_1_checked, root7Node53Step1Chunk3_2_checked, root7Node53Step1Chunk3_3_checked, root7Node53Step1Chunk3_4_checked, root7Node53Step1Chunk3_5_checked, root7Node53Step1Chunk4_0_checked, root7Node53Step1Chunk4_1_checked, root7Node53Step1Chunk4_2_checked, root7Node53Step1Chunk4_3_checked, root7Node53Step1Chunk4_4_checked, root7Node53Step1Chunk4_5_checked, root7Node53Step1Chunk5_0_checked, root7Node53Step1Chunk5_1_checked, root7Node53Step1Chunk5_2_checked, root7Node53Step1Chunk5_3_checked, root7Node53Step1Chunk5_4_checked, root7Node53Step1Chunk5_5_checked, root7Node53Step1Chunk6_0_checked, root7Node53Step1Chunk6_1_checked, root7Node53Step1Chunk6_2_checked, root7Node53Step1Chunk6_3_checked, root7Node53Step1Chunk6_4_checked, root7Node53Step1Chunk6_5_checked, root7Node53Step1Chunk7_0_checked, root7Node53Step1Chunk7_1_checked, root7Node53Step1Chunk7_2_checked, root7Node53Step1Chunk7_3_checked, root7Node53Step1Chunk7_4_checked, root7Node53Step1Chunk7_5_checked, root7Node53Step1Chunk8_0_checked, root7Node53Step1Chunk8_1_checked, root7Node53Step1Chunk8_2_checked, root7Node53Step1Chunk8_3_checked, root7Node53Step1Chunk8_4_checked, root7Node53Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node53Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node53Domains1 (.output 24) = true := by decide
def root7Node54Domains0 : Domains 61 State := restrict root7Node52Domains1 34 (4,3)
def root7Node54Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(2,5)]
  | 44 => some [(6,0)]
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
theorem root7Node54Domains0_fast_eq : root7Node54Domains0 = expandDomains root7Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node54Domains0 v = expandDomains root7Node54Domains0Fast v from by decide) v
def root7Node54Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(1,4)]
  | 43 => [(2,5)]
  | 44 => [(6,0)]
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
def root7Node54Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(1,4)]
  | 43 => some [(2,5)]
  | 44 => some [(6,0)]
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
theorem root7Node54Domains1_fast_eq : root7Node54Domains1 = expandDomains root7Node54Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node54Domains1 v = expandDomains root7Node54Domains1Fast v from by decide) v
theorem root7Node54Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1_checked :
    checkReplacement table16 root7Node54Domains0 root7Node54Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node54Step1Chunk0_0_checked, root7Node54Step1Chunk0_1_checked, root7Node54Step1Chunk0_2_checked, root7Node54Step1Chunk0_3_checked, root7Node54Step1Chunk0_4_checked, root7Node54Step1Chunk0_5_checked, root7Node54Step1Chunk1_0_checked, root7Node54Step1Chunk1_1_checked, root7Node54Step1Chunk1_2_checked, root7Node54Step1Chunk1_3_checked, root7Node54Step1Chunk1_4_checked, root7Node54Step1Chunk1_5_checked, root7Node54Step1Chunk2_0_checked, root7Node54Step1Chunk2_1_checked, root7Node54Step1Chunk2_2_checked, root7Node54Step1Chunk2_3_checked, root7Node54Step1Chunk2_4_checked, root7Node54Step1Chunk2_5_checked, root7Node54Step1Chunk3_0_checked, root7Node54Step1Chunk3_1_checked, root7Node54Step1Chunk3_2_checked, root7Node54Step1Chunk3_3_checked, root7Node54Step1Chunk3_4_checked, root7Node54Step1Chunk3_5_checked, root7Node54Step1Chunk4_0_checked, root7Node54Step1Chunk4_1_checked, root7Node54Step1Chunk4_2_checked, root7Node54Step1Chunk4_3_checked, root7Node54Step1Chunk4_4_checked, root7Node54Step1Chunk4_5_checked, root7Node54Step1Chunk5_0_checked, root7Node54Step1Chunk5_1_checked, root7Node54Step1Chunk5_2_checked, root7Node54Step1Chunk5_3_checked, root7Node54Step1Chunk5_4_checked, root7Node54Step1Chunk5_5_checked, root7Node54Step1Chunk6_0_checked, root7Node54Step1Chunk6_1_checked, root7Node54Step1Chunk6_2_checked, root7Node54Step1Chunk6_3_checked, root7Node54Step1Chunk6_4_checked, root7Node54Step1Chunk6_5_checked, root7Node54Step1Chunk7_0_checked, root7Node54Step1Chunk7_1_checked, root7Node54Step1Chunk7_2_checked, root7Node54Step1Chunk7_3_checked, root7Node54Step1Chunk7_4_checked, root7Node54Step1Chunk7_5_checked, root7Node54Step1Chunk8_0_checked, root7Node54Step1Chunk8_1_checked, root7Node54Step1Chunk8_2_checked, root7Node54Step1Chunk8_3_checked, root7Node54Step1Chunk8_4_checked, root7Node54Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node54Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node54Domains1 (.output 25) = true := by decide
def root7Node55Domains0 : Domains 61 State := restrict root7Node49Domains1 29 (8,5)
def root7Node55Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4),(3,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(0,0),(1,4),(6,4),(7,4)]
  | 43 => some [(2,3),(2,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(1,5),(4,1),(7,5),(8,1)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2),(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0),(1,4),(6,4)]
theorem root7Node55Domains0_fast_eq : root7Node55Domains0 = expandDomains root7Node55Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node55Domains0 v = expandDomains root7Node55Domains0Fast v from by decide) v
def root7Node55Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(2,3),(2,5),(4,3)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(2,3),(2,5)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(1,2),(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node55Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(2,3),(2,5),(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(2,3),(2,5)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node55Domains1_fast_eq : root7Node55Domains1 = expandDomains root7Node55Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node55Domains1 v = expandDomains root7Node55Domains1Fast v from by decide) v
theorem root7Node55Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node55Domains0 root7Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains0 root7Node55Domains1
    root7Node55Domains0Fast root7Node55Domains1Fast
    root7Node55Domains0_fast_eq root7Node55Domains1_fast_eq (by decide)
theorem root7Node55Step1_checked :
    checkReplacement table39 root7Node55Domains0 root7Node55Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node55Step1Chunk0_0_checked, root7Node55Step1Chunk0_1_checked, root7Node55Step1Chunk0_2_checked, root7Node55Step1Chunk0_3_checked, root7Node55Step1Chunk0_4_checked, root7Node55Step1Chunk0_5_checked, root7Node55Step1Chunk1_0_checked, root7Node55Step1Chunk1_1_checked, root7Node55Step1Chunk1_2_checked, root7Node55Step1Chunk1_3_checked, root7Node55Step1Chunk1_4_checked, root7Node55Step1Chunk1_5_checked, root7Node55Step1Chunk2_0_checked, root7Node55Step1Chunk2_1_checked, root7Node55Step1Chunk2_2_checked, root7Node55Step1Chunk2_3_checked, root7Node55Step1Chunk2_4_checked, root7Node55Step1Chunk2_5_checked, root7Node55Step1Chunk3_0_checked, root7Node55Step1Chunk3_1_checked, root7Node55Step1Chunk3_2_checked, root7Node55Step1Chunk3_3_checked, root7Node55Step1Chunk3_4_checked, root7Node55Step1Chunk3_5_checked, root7Node55Step1Chunk4_0_checked, root7Node55Step1Chunk4_1_checked, root7Node55Step1Chunk4_2_checked, root7Node55Step1Chunk4_3_checked, root7Node55Step1Chunk4_4_checked, root7Node55Step1Chunk4_5_checked, root7Node55Step1Chunk5_0_checked, root7Node55Step1Chunk5_1_checked, root7Node55Step1Chunk5_2_checked, root7Node55Step1Chunk5_3_checked, root7Node55Step1Chunk5_4_checked, root7Node55Step1Chunk5_5_checked, root7Node55Step1Chunk6_0_checked, root7Node55Step1Chunk6_1_checked, root7Node55Step1Chunk6_2_checked, root7Node55Step1Chunk6_3_checked, root7Node55Step1Chunk6_4_checked, root7Node55Step1Chunk6_5_checked, root7Node55Step1Chunk7_0_checked, root7Node55Step1Chunk7_1_checked, root7Node55Step1Chunk7_2_checked, root7Node55Step1Chunk7_3_checked, root7Node55Step1Chunk7_4_checked, root7Node55Step1Chunk7_5_checked, root7Node55Step1Chunk8_0_checked, root7Node55Step1Chunk8_1_checked, root7Node55Step1Chunk8_2_checked, root7Node55Step1Chunk8_3_checked, root7Node55Step1Chunk8_4_checked, root7Node55Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node55Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(2,3),(2,5)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(1,2),(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node55Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(2,3),(2,5)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node55Domains2_fast_eq : root7Node55Domains2 = expandDomains root7Node55Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node55Domains2 v = expandDomains root7Node55Domains2Fast v from by decide) v
theorem root7Node55Step2Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root7Node55Domains1 root7Node55Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains1 root7Node55Domains2
    root7Node55Domains1Fast root7Node55Domains2Fast
    root7Node55Domains1_fast_eq root7Node55Domains2_fast_eq (by decide)
theorem root7Node55Step2_checked :
    checkReplacement table10 root7Node55Domains1 root7Node55Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node55Step2Chunk0_0_checked, root7Node55Step2Chunk0_1_checked, root7Node55Step2Chunk0_2_checked, root7Node55Step2Chunk0_3_checked, root7Node55Step2Chunk0_4_checked, root7Node55Step2Chunk0_5_checked, root7Node55Step2Chunk1_0_checked, root7Node55Step2Chunk1_1_checked, root7Node55Step2Chunk1_2_checked, root7Node55Step2Chunk1_3_checked, root7Node55Step2Chunk1_4_checked, root7Node55Step2Chunk1_5_checked, root7Node55Step2Chunk2_0_checked, root7Node55Step2Chunk2_1_checked, root7Node55Step2Chunk2_2_checked, root7Node55Step2Chunk2_3_checked, root7Node55Step2Chunk2_4_checked, root7Node55Step2Chunk2_5_checked, root7Node55Step2Chunk3_0_checked, root7Node55Step2Chunk3_1_checked, root7Node55Step2Chunk3_2_checked, root7Node55Step2Chunk3_3_checked, root7Node55Step2Chunk3_4_checked, root7Node55Step2Chunk3_5_checked, root7Node55Step2Chunk4_0_checked, root7Node55Step2Chunk4_1_checked, root7Node55Step2Chunk4_2_checked, root7Node55Step2Chunk4_3_checked, root7Node55Step2Chunk4_4_checked, root7Node55Step2Chunk4_5_checked, root7Node55Step2Chunk5_0_checked, root7Node55Step2Chunk5_1_checked, root7Node55Step2Chunk5_2_checked, root7Node55Step2Chunk5_3_checked, root7Node55Step2Chunk5_4_checked, root7Node55Step2Chunk5_5_checked, root7Node55Step2Chunk6_0_checked, root7Node55Step2Chunk6_1_checked, root7Node55Step2Chunk6_2_checked, root7Node55Step2Chunk6_3_checked, root7Node55Step2Chunk6_4_checked, root7Node55Step2Chunk6_5_checked, root7Node55Step2Chunk7_0_checked, root7Node55Step2Chunk7_1_checked, root7Node55Step2Chunk7_2_checked, root7Node55Step2Chunk7_3_checked, root7Node55Step2Chunk7_4_checked, root7Node55Step2Chunk7_5_checked, root7Node55Step2Chunk8_0_checked, root7Node55Step2Chunk8_1_checked, root7Node55Step2Chunk8_2_checked, root7Node55Step2Chunk8_3_checked, root7Node55Step2Chunk8_4_checked, root7Node55Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node55Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(2,3)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(1,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node55Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(2,3)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(1,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node55Domains3_fast_eq : root7Node55Domains3 = expandDomains root7Node55Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node55Domains3 v = expandDomains root7Node55Domains3Fast v from by decide) v
theorem root7Node55Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node55Domains2 root7Node55Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node55Domains2 root7Node55Domains3
    root7Node55Domains2Fast root7Node55Domains3Fast
    root7Node55Domains2_fast_eq root7Node55Domains3_fast_eq (by decide)
theorem root7Node55Step3_checked :
    checkReplacement table26 root7Node55Domains2 root7Node55Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node55Step3Chunk0_0_checked, root7Node55Step3Chunk0_1_checked, root7Node55Step3Chunk0_2_checked, root7Node55Step3Chunk0_3_checked, root7Node55Step3Chunk0_4_checked, root7Node55Step3Chunk0_5_checked, root7Node55Step3Chunk1_0_checked, root7Node55Step3Chunk1_1_checked, root7Node55Step3Chunk1_2_checked, root7Node55Step3Chunk1_3_checked, root7Node55Step3Chunk1_4_checked, root7Node55Step3Chunk1_5_checked, root7Node55Step3Chunk2_0_checked, root7Node55Step3Chunk2_1_checked, root7Node55Step3Chunk2_2_checked, root7Node55Step3Chunk2_3_checked, root7Node55Step3Chunk2_4_checked, root7Node55Step3Chunk2_5_checked, root7Node55Step3Chunk3_0_checked, root7Node55Step3Chunk3_1_checked, root7Node55Step3Chunk3_2_checked, root7Node55Step3Chunk3_3_checked, root7Node55Step3Chunk3_4_checked, root7Node55Step3Chunk3_5_checked, root7Node55Step3Chunk4_0_checked, root7Node55Step3Chunk4_1_checked, root7Node55Step3Chunk4_2_checked, root7Node55Step3Chunk4_3_checked, root7Node55Step3Chunk4_4_checked, root7Node55Step3Chunk4_5_checked, root7Node55Step3Chunk5_0_checked, root7Node55Step3Chunk5_1_checked, root7Node55Step3Chunk5_2_checked, root7Node55Step3Chunk5_3_checked, root7Node55Step3Chunk5_4_checked, root7Node55Step3Chunk5_5_checked, root7Node55Step3Chunk6_0_checked, root7Node55Step3Chunk6_1_checked, root7Node55Step3Chunk6_2_checked, root7Node55Step3Chunk6_3_checked, root7Node55Step3Chunk6_4_checked, root7Node55Step3Chunk6_5_checked, root7Node55Step3Chunk7_0_checked, root7Node55Step3Chunk7_1_checked, root7Node55Step3Chunk7_2_checked, root7Node55Step3Chunk7_3_checked, root7Node55Step3Chunk7_4_checked, root7Node55Step3Chunk7_5_checked, root7Node55Step3Chunk8_0_checked, root7Node55Step3Chunk8_1_checked, root7Node55Step3Chunk8_2_checked, root7Node55Step3Chunk8_3_checked, root7Node55Step3Chunk8_4_checked, root7Node55Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
