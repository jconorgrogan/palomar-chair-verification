module

public import SpectreFinite.RadiusFourRoot8Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node44Domains0 : Domains 61 State := restrict root8Node42Domains2 55 (8,5)
def root8Node44Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(3,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(2,4)]
  | 28 => some [(1,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root8Node44Domains0_fast_eq : root8Node44Domains0 = expandDomains root8Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node44Domains0 v = expandDomains root8Node44Domains0Fast v from by decide) v
def root8Node44Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(3,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(2,4)]
  | 28 => [(1,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(3,4)]
  | _ => [(6,3)]
def root8Node44Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(3,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(2,4)]
  | 28 => some [(1,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(3,4)]
  | _ => some [(6,3)]
theorem root8Node44Domains1_fast_eq : root8Node44Domains1 = expandDomains root8Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node44Domains1 v = expandDomains root8Node44Domains1Fast v from by decide) v
theorem root8Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1_checked :
    checkReplacement table39 root8Node44Domains0 root8Node44Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node44Step1Chunk0_0_checked, root8Node44Step1Chunk0_1_checked, root8Node44Step1Chunk0_2_checked, root8Node44Step1Chunk0_3_checked, root8Node44Step1Chunk0_4_checked, root8Node44Step1Chunk0_5_checked, root8Node44Step1Chunk1_0_checked, root8Node44Step1Chunk1_1_checked, root8Node44Step1Chunk1_2_checked, root8Node44Step1Chunk1_3_checked, root8Node44Step1Chunk1_4_checked, root8Node44Step1Chunk1_5_checked, root8Node44Step1Chunk2_0_checked, root8Node44Step1Chunk2_1_checked, root8Node44Step1Chunk2_2_checked, root8Node44Step1Chunk2_3_checked, root8Node44Step1Chunk2_4_checked, root8Node44Step1Chunk2_5_checked, root8Node44Step1Chunk3_0_checked, root8Node44Step1Chunk3_1_checked, root8Node44Step1Chunk3_2_checked, root8Node44Step1Chunk3_3_checked, root8Node44Step1Chunk3_4_checked, root8Node44Step1Chunk3_5_checked, root8Node44Step1Chunk4_0_checked, root8Node44Step1Chunk4_1_checked, root8Node44Step1Chunk4_2_checked, root8Node44Step1Chunk4_3_checked, root8Node44Step1Chunk4_4_checked, root8Node44Step1Chunk4_5_checked, root8Node44Step1Chunk5_0_checked, root8Node44Step1Chunk5_1_checked, root8Node44Step1Chunk5_2_checked, root8Node44Step1Chunk5_3_checked, root8Node44Step1Chunk5_4_checked, root8Node44Step1Chunk5_5_checked, root8Node44Step1Chunk6_0_checked, root8Node44Step1Chunk6_1_checked, root8Node44Step1Chunk6_2_checked, root8Node44Step1Chunk6_3_checked, root8Node44Step1Chunk6_4_checked, root8Node44Step1Chunk6_5_checked, root8Node44Step1Chunk7_0_checked, root8Node44Step1Chunk7_1_checked, root8Node44Step1Chunk7_2_checked, root8Node44Step1Chunk7_3_checked, root8Node44Step1Chunk7_4_checked, root8Node44Step1Chunk7_5_checked, root8Node44Step1Chunk8_0_checked, root8Node44Step1Chunk8_1_checked, root8Node44Step1Chunk8_2_checked, root8Node44Step1Chunk8_3_checked, root8Node44Step1Chunk8_4_checked, root8Node44Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node44Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node44Domains1 (.output 21) = true := by decide
def root8Node45Domains0 : Domains 61 State := restrict root8Node41Domains1 18 (7,5)
def root8Node45Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(2,2),(2,4)]
  | 28 => some [(1,3),(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(7,4)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(5,1),(8,1)]
  | 57 => some [(0,1),(6,5)]
  | 58 => some [(0,4),(6,2)]
  | 59 => some [(1,4),(3,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root8Node45Domains0_fast_eq : root8Node45Domains0 = expandDomains root8Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node45Domains0 v = expandDomains root8Node45Domains0Fast v from by decide) v
def root8Node45Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(6,3)]
  | 27 => [(2,2)]
  | 28 => [(3,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(1,1)]
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
  | 55 => [(5,5),(8,5)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(1,4),(3,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root8Node45Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(6,3)]
  | 27 => some [(2,2)]
  | 28 => some [(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(1,1)]
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
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(1,4),(3,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root8Node45Domains1_fast_eq : root8Node45Domains1 = expandDomains root8Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node45Domains1 v = expandDomains root8Node45Domains1Fast v from by decide) v
theorem root8Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1_checked :
    checkReplacement table37 root8Node45Domains0 root8Node45Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node45Step1Chunk0_0_checked, root8Node45Step1Chunk0_1_checked, root8Node45Step1Chunk0_2_checked, root8Node45Step1Chunk0_3_checked, root8Node45Step1Chunk0_4_checked, root8Node45Step1Chunk0_5_checked, root8Node45Step1Chunk1_0_checked, root8Node45Step1Chunk1_1_checked, root8Node45Step1Chunk1_2_checked, root8Node45Step1Chunk1_3_checked, root8Node45Step1Chunk1_4_checked, root8Node45Step1Chunk1_5_checked, root8Node45Step1Chunk2_0_checked, root8Node45Step1Chunk2_1_checked, root8Node45Step1Chunk2_2_checked, root8Node45Step1Chunk2_3_checked, root8Node45Step1Chunk2_4_checked, root8Node45Step1Chunk2_5_checked, root8Node45Step1Chunk3_0_checked, root8Node45Step1Chunk3_1_checked, root8Node45Step1Chunk3_2_checked, root8Node45Step1Chunk3_3_checked, root8Node45Step1Chunk3_4_checked, root8Node45Step1Chunk3_5_checked, root8Node45Step1Chunk4_0_checked, root8Node45Step1Chunk4_1_checked, root8Node45Step1Chunk4_2_checked, root8Node45Step1Chunk4_3_checked, root8Node45Step1Chunk4_4_checked, root8Node45Step1Chunk4_5_checked, root8Node45Step1Chunk5_0_checked, root8Node45Step1Chunk5_1_checked, root8Node45Step1Chunk5_2_checked, root8Node45Step1Chunk5_3_checked, root8Node45Step1Chunk5_4_checked, root8Node45Step1Chunk5_5_checked, root8Node45Step1Chunk6_0_checked, root8Node45Step1Chunk6_1_checked, root8Node45Step1Chunk6_2_checked, root8Node45Step1Chunk6_3_checked, root8Node45Step1Chunk6_4_checked, root8Node45Step1Chunk6_5_checked, root8Node45Step1Chunk7_0_checked, root8Node45Step1Chunk7_1_checked, root8Node45Step1Chunk7_2_checked, root8Node45Step1Chunk7_3_checked, root8Node45Step1Chunk7_4_checked, root8Node45Step1Chunk7_5_checked, root8Node45Step1Chunk8_0_checked, root8Node45Step1Chunk8_1_checked, root8Node45Step1Chunk8_2_checked, root8Node45Step1Chunk8_3_checked, root8Node45Step1Chunk8_4_checked, root8Node45Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node45Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(6,3)]
  | 27 => [(2,2)]
  | 28 => [(3,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(1,1)]
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
def root8Node45Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(6,3)]
  | 27 => some [(2,2)]
  | 28 => some [(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(1,1)]
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
theorem root8Node45Domains2_fast_eq : root8Node45Domains2 = expandDomains root8Node45Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node45Domains2 v = expandDomains root8Node45Domains2Fast v from by decide) v
theorem root8Node45Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node45Domains1 root8Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains1 root8Node45Domains2
    root8Node45Domains1Fast root8Node45Domains2Fast
    root8Node45Domains1_fast_eq root8Node45Domains2_fast_eq (by decide)
theorem root8Node45Step2_checked :
    checkReplacement table39 root8Node45Domains1 root8Node45Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node45Step2Chunk0_0_checked, root8Node45Step2Chunk0_1_checked, root8Node45Step2Chunk0_2_checked, root8Node45Step2Chunk0_3_checked, root8Node45Step2Chunk0_4_checked, root8Node45Step2Chunk0_5_checked, root8Node45Step2Chunk1_0_checked, root8Node45Step2Chunk1_1_checked, root8Node45Step2Chunk1_2_checked, root8Node45Step2Chunk1_3_checked, root8Node45Step2Chunk1_4_checked, root8Node45Step2Chunk1_5_checked, root8Node45Step2Chunk2_0_checked, root8Node45Step2Chunk2_1_checked, root8Node45Step2Chunk2_2_checked, root8Node45Step2Chunk2_3_checked, root8Node45Step2Chunk2_4_checked, root8Node45Step2Chunk2_5_checked, root8Node45Step2Chunk3_0_checked, root8Node45Step2Chunk3_1_checked, root8Node45Step2Chunk3_2_checked, root8Node45Step2Chunk3_3_checked, root8Node45Step2Chunk3_4_checked, root8Node45Step2Chunk3_5_checked, root8Node45Step2Chunk4_0_checked, root8Node45Step2Chunk4_1_checked, root8Node45Step2Chunk4_2_checked, root8Node45Step2Chunk4_3_checked, root8Node45Step2Chunk4_4_checked, root8Node45Step2Chunk4_5_checked, root8Node45Step2Chunk5_0_checked, root8Node45Step2Chunk5_1_checked, root8Node45Step2Chunk5_2_checked, root8Node45Step2Chunk5_3_checked, root8Node45Step2Chunk5_4_checked, root8Node45Step2Chunk5_5_checked, root8Node45Step2Chunk6_0_checked, root8Node45Step2Chunk6_1_checked, root8Node45Step2Chunk6_2_checked, root8Node45Step2Chunk6_3_checked, root8Node45Step2Chunk6_4_checked, root8Node45Step2Chunk6_5_checked, root8Node45Step2Chunk7_0_checked, root8Node45Step2Chunk7_1_checked, root8Node45Step2Chunk7_2_checked, root8Node45Step2Chunk7_3_checked, root8Node45Step2Chunk7_4_checked, root8Node45Step2Chunk7_5_checked, root8Node45Step2Chunk8_0_checked, root8Node45Step2Chunk8_1_checked, root8Node45Step2Chunk8_2_checked, root8Node45Step2Chunk8_3_checked, root8Node45Step2Chunk8_4_checked, root8Node45Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node45Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node45Domains2 (.output 22) = true := by decide
def root8Node46Domains0 : Domains 61 State := restrict root8Node0Domains5 22 (7,1)
def root8Node46Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,5)]
  | 6 => some [(4,0),(4,2),(7,0),(8,0)]
  | 7 => some [(5,3),(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(1,0),(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
  | 12 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(4,0),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1)]
  | 24 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(4,2),(5,2),(5,5),(8,2)]
  | 33 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(4,1),(7,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5),(7,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2),(8,2)]
  | 54 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
theorem root8Node46Domains0_fast_eq : root8Node46Domains0 = expandDomains root8Node46Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node46Domains0 v = expandDomains root8Node46Domains0Fast v from by decide) v
def root8Node46Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => [(4,4),(5,1),(5,4),(8,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 18 => [(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 35 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(4,4),(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(7,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5),(7,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2),(8,2)]
  | 54 => [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
def root8Node46Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0)]
  | 1 => some [(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => some [(4,4),(5,1),(5,4),(8,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 18 => some [(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(4,4),(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(7,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5),(7,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2),(8,2)]
  | 54 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
theorem root8Node46Domains1_fast_eq : root8Node46Domains1 = expandDomains root8Node46Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node46Domains1 v = expandDomains root8Node46Domains1Fast v from by decide) v
theorem root8Node46Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root8Node46Domains0 root8Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains0 root8Node46Domains1
    root8Node46Domains0Fast root8Node46Domains1Fast
    root8Node46Domains0_fast_eq root8Node46Domains1_fast_eq (by decide)
theorem root8Node46Step1_checked :
    checkReplacement table21 root8Node46Domains0 root8Node46Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node46Step1Chunk0_0_checked, root8Node46Step1Chunk0_1_checked, root8Node46Step1Chunk0_2_checked, root8Node46Step1Chunk0_3_checked, root8Node46Step1Chunk0_4_checked, root8Node46Step1Chunk0_5_checked, root8Node46Step1Chunk1_0_checked, root8Node46Step1Chunk1_1_checked, root8Node46Step1Chunk1_2_checked, root8Node46Step1Chunk1_3_checked, root8Node46Step1Chunk1_4_checked, root8Node46Step1Chunk1_5_checked, root8Node46Step1Chunk2_0_checked, root8Node46Step1Chunk2_1_checked, root8Node46Step1Chunk2_2_checked, root8Node46Step1Chunk2_3_checked, root8Node46Step1Chunk2_4_checked, root8Node46Step1Chunk2_5_checked, root8Node46Step1Chunk3_0_checked, root8Node46Step1Chunk3_1_checked, root8Node46Step1Chunk3_2_checked, root8Node46Step1Chunk3_3_checked, root8Node46Step1Chunk3_4_checked, root8Node46Step1Chunk3_5_checked, root8Node46Step1Chunk4_0_checked, root8Node46Step1Chunk4_1_checked, root8Node46Step1Chunk4_2_checked, root8Node46Step1Chunk4_3_checked, root8Node46Step1Chunk4_4_checked, root8Node46Step1Chunk4_5_checked, root8Node46Step1Chunk5_0_checked, root8Node46Step1Chunk5_1_checked, root8Node46Step1Chunk5_2_checked, root8Node46Step1Chunk5_3_checked, root8Node46Step1Chunk5_4_checked, root8Node46Step1Chunk5_5_checked, root8Node46Step1Chunk6_0_checked, root8Node46Step1Chunk6_1_checked, root8Node46Step1Chunk6_2_checked, root8Node46Step1Chunk6_3_checked, root8Node46Step1Chunk6_4_checked, root8Node46Step1Chunk6_5_checked, root8Node46Step1Chunk7_0_checked, root8Node46Step1Chunk7_1_checked, root8Node46Step1Chunk7_2_checked, root8Node46Step1Chunk7_3_checked, root8Node46Step1Chunk7_4_checked, root8Node46Step1Chunk7_5_checked, root8Node46Step1Chunk8_0_checked, root8Node46Step1Chunk8_1_checked, root8Node46Step1Chunk8_2_checked, root8Node46Step1Chunk8_3_checked, root8Node46Step1Chunk8_4_checked, root8Node46Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node46Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => [(4,4),(5,1),(5,4),(8,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(4,5),(5,5),(8,5)]
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
def root8Node46Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0)]
  | 1 => some [(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
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
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(4,5),(5,5),(8,5)]
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
theorem root8Node46Domains2_fast_eq : root8Node46Domains2 = expandDomains root8Node46Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node46Domains2 v = expandDomains root8Node46Domains2Fast v from by decide) v
theorem root8Node46Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node46Domains1 root8Node46Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains1 root8Node46Domains2
    root8Node46Domains1Fast root8Node46Domains2Fast
    root8Node46Domains1_fast_eq root8Node46Domains2_fast_eq (by decide)
theorem root8Node46Step2_checked :
    checkReplacement table40 root8Node46Domains1 root8Node46Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node46Step2Chunk0_0_checked, root8Node46Step2Chunk0_1_checked, root8Node46Step2Chunk0_2_checked, root8Node46Step2Chunk0_3_checked, root8Node46Step2Chunk0_4_checked, root8Node46Step2Chunk0_5_checked, root8Node46Step2Chunk1_0_checked, root8Node46Step2Chunk1_1_checked, root8Node46Step2Chunk1_2_checked, root8Node46Step2Chunk1_3_checked, root8Node46Step2Chunk1_4_checked, root8Node46Step2Chunk1_5_checked, root8Node46Step2Chunk2_0_checked, root8Node46Step2Chunk2_1_checked, root8Node46Step2Chunk2_2_checked, root8Node46Step2Chunk2_3_checked, root8Node46Step2Chunk2_4_checked, root8Node46Step2Chunk2_5_checked, root8Node46Step2Chunk3_0_checked, root8Node46Step2Chunk3_1_checked, root8Node46Step2Chunk3_2_checked, root8Node46Step2Chunk3_3_checked, root8Node46Step2Chunk3_4_checked, root8Node46Step2Chunk3_5_checked, root8Node46Step2Chunk4_0_checked, root8Node46Step2Chunk4_1_checked, root8Node46Step2Chunk4_2_checked, root8Node46Step2Chunk4_3_checked, root8Node46Step2Chunk4_4_checked, root8Node46Step2Chunk4_5_checked, root8Node46Step2Chunk5_0_checked, root8Node46Step2Chunk5_1_checked, root8Node46Step2Chunk5_2_checked, root8Node46Step2Chunk5_3_checked, root8Node46Step2Chunk5_4_checked, root8Node46Step2Chunk5_5_checked, root8Node46Step2Chunk6_0_checked, root8Node46Step2Chunk6_1_checked, root8Node46Step2Chunk6_2_checked, root8Node46Step2Chunk6_3_checked, root8Node46Step2Chunk6_4_checked, root8Node46Step2Chunk6_5_checked, root8Node46Step2Chunk7_0_checked, root8Node46Step2Chunk7_1_checked, root8Node46Step2Chunk7_2_checked, root8Node46Step2Chunk7_3_checked, root8Node46Step2Chunk7_4_checked, root8Node46Step2Chunk7_5_checked, root8Node46Step2Chunk8_0_checked, root8Node46Step2Chunk8_1_checked, root8Node46Step2Chunk8_2_checked, root8Node46Step2Chunk8_3_checked, root8Node46Step2Chunk8_4_checked, root8Node46Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
