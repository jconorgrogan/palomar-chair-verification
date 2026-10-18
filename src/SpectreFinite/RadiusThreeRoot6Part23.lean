module

public import SpectreFinite.RadiusThreeRoot6Part22
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node44Domains0 : Domains 37 State := restrict root6Node42Domains1 22 (8,0)
def root6Node44Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(3,5)]
  | 8 => some [(0,3)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(6,5)]
  | 21 => some [(0,4)]
  | 22 => some [(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(6,4)]
  | 29 => some [(1,2),(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node44Domains0_fast_eq : root6Node44Domains0 = expandDomains root6Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node44Domains0 v = expandDomains root6Node44Domains0Fast v from by decide) v
def root6Node44Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(5,5)]
  | 5 => [(7,0)]
  | 6 => [(4,3)]
  | 7 => [(3,5)]
  | 8 => [(0,3)]
  | 9 => [(0,5)]
  | 10 => [(4,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,4)]
  | 14 => [(1,3)]
  | 15 => [(6,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(6,5)]
  | 21 => [(0,4)]
  | 22 => [(8,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(6,4)]
  | 29 => [(1,2)]
  | 30 => [(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node44Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(5,5)]
  | 5 => some [(7,0)]
  | 6 => some [(4,3)]
  | 7 => some [(3,5)]
  | 8 => some [(0,3)]
  | 9 => some [(0,5)]
  | 10 => some [(4,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(6,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(6,5)]
  | 21 => some [(0,4)]
  | 22 => some [(8,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node44Domains1_fast_eq : root6Node44Domains1 = expandDomains root6Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node44Domains1 v = expandDomains root6Node44Domains1Fast v from by decide) v
theorem root6Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node44Domains0 root6Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node44Domains0 root6Node44Domains1
    root6Node44Domains0Fast root6Node44Domains1Fast
    root6Node44Domains0_fast_eq root6Node44Domains1_fast_eq (by decide)
theorem root6Node44Step1_checked :
    checkReplacement table23 root6Node44Domains0 root6Node44Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node44Step1Chunk0_0_checked, root6Node44Step1Chunk0_1_checked, root6Node44Step1Chunk0_2_checked, root6Node44Step1Chunk0_3_checked, root6Node44Step1Chunk0_4_checked, root6Node44Step1Chunk0_5_checked, root6Node44Step1Chunk1_0_checked, root6Node44Step1Chunk1_1_checked, root6Node44Step1Chunk1_2_checked, root6Node44Step1Chunk1_3_checked, root6Node44Step1Chunk1_4_checked, root6Node44Step1Chunk1_5_checked, root6Node44Step1Chunk2_0_checked, root6Node44Step1Chunk2_1_checked, root6Node44Step1Chunk2_2_checked, root6Node44Step1Chunk2_3_checked, root6Node44Step1Chunk2_4_checked, root6Node44Step1Chunk2_5_checked, root6Node44Step1Chunk3_0_checked, root6Node44Step1Chunk3_1_checked, root6Node44Step1Chunk3_2_checked, root6Node44Step1Chunk3_3_checked, root6Node44Step1Chunk3_4_checked, root6Node44Step1Chunk3_5_checked, root6Node44Step1Chunk4_0_checked, root6Node44Step1Chunk4_1_checked, root6Node44Step1Chunk4_2_checked, root6Node44Step1Chunk4_3_checked, root6Node44Step1Chunk4_4_checked, root6Node44Step1Chunk4_5_checked, root6Node44Step1Chunk5_0_checked, root6Node44Step1Chunk5_1_checked, root6Node44Step1Chunk5_2_checked, root6Node44Step1Chunk5_3_checked, root6Node44Step1Chunk5_4_checked, root6Node44Step1Chunk5_5_checked, root6Node44Step1Chunk6_0_checked, root6Node44Step1Chunk6_1_checked, root6Node44Step1Chunk6_2_checked, root6Node44Step1Chunk6_3_checked, root6Node44Step1Chunk6_4_checked, root6Node44Step1Chunk6_5_checked, root6Node44Step1Chunk7_0_checked, root6Node44Step1Chunk7_1_checked, root6Node44Step1Chunk7_2_checked, root6Node44Step1Chunk7_3_checked, root6Node44Step1Chunk7_4_checked, root6Node44Step1Chunk7_5_checked, root6Node44Step1Chunk8_0_checked, root6Node44Step1Chunk8_1_checked, root6Node44Step1Chunk8_2_checked, root6Node44Step1Chunk8_3_checked, root6Node44Step1Chunk8_4_checked, root6Node44Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node44Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node44Domains1 (.output 22) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
