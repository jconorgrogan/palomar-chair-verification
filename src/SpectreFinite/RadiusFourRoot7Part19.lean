module

public import SpectreFinite.RadiusFourRoot7Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node56Domains0 : Domains 61 State := restrict root7Node55Domains3 49 (4,1)
def root7Node56Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 49 => some [(4,1)]
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
theorem root7Node56Domains0_fast_eq : root7Node56Domains0 = expandDomains root7Node56Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node56Domains0 v = expandDomains root7Node56Domains0Fast v from by decide) v
def root7Node56Domains1 (v : Fin 61) : List State :=
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
  | 49 => [(4,1)]
  | 50 => [(1,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(6,4)]
def root7Node56Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 49 => some [(4,1)]
  | 50 => some [(1,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(6,4)]
theorem root7Node56Domains1_fast_eq : root7Node56Domains1 = expandDomains root7Node56Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node56Domains1 v = expandDomains root7Node56Domains1Fast v from by decide) v
theorem root7Node56Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1_checked :
    checkReplacement table39 root7Node56Domains0 root7Node56Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node56Step1Chunk0_0_checked, root7Node56Step1Chunk0_1_checked, root7Node56Step1Chunk0_2_checked, root7Node56Step1Chunk0_3_checked, root7Node56Step1Chunk0_4_checked, root7Node56Step1Chunk0_5_checked, root7Node56Step1Chunk1_0_checked, root7Node56Step1Chunk1_1_checked, root7Node56Step1Chunk1_2_checked, root7Node56Step1Chunk1_3_checked, root7Node56Step1Chunk1_4_checked, root7Node56Step1Chunk1_5_checked, root7Node56Step1Chunk2_0_checked, root7Node56Step1Chunk2_1_checked, root7Node56Step1Chunk2_2_checked, root7Node56Step1Chunk2_3_checked, root7Node56Step1Chunk2_4_checked, root7Node56Step1Chunk2_5_checked, root7Node56Step1Chunk3_0_checked, root7Node56Step1Chunk3_1_checked, root7Node56Step1Chunk3_2_checked, root7Node56Step1Chunk3_3_checked, root7Node56Step1Chunk3_4_checked, root7Node56Step1Chunk3_5_checked, root7Node56Step1Chunk4_0_checked, root7Node56Step1Chunk4_1_checked, root7Node56Step1Chunk4_2_checked, root7Node56Step1Chunk4_3_checked, root7Node56Step1Chunk4_4_checked, root7Node56Step1Chunk4_5_checked, root7Node56Step1Chunk5_0_checked, root7Node56Step1Chunk5_1_checked, root7Node56Step1Chunk5_2_checked, root7Node56Step1Chunk5_3_checked, root7Node56Step1Chunk5_4_checked, root7Node56Step1Chunk5_5_checked, root7Node56Step1Chunk6_0_checked, root7Node56Step1Chunk6_1_checked, root7Node56Step1Chunk6_2_checked, root7Node56Step1Chunk6_3_checked, root7Node56Step1Chunk6_4_checked, root7Node56Step1Chunk6_5_checked, root7Node56Step1Chunk7_0_checked, root7Node56Step1Chunk7_1_checked, root7Node56Step1Chunk7_2_checked, root7Node56Step1Chunk7_3_checked, root7Node56Step1Chunk7_4_checked, root7Node56Step1Chunk7_5_checked, root7Node56Step1Chunk8_0_checked, root7Node56Step1Chunk8_1_checked, root7Node56Step1Chunk8_2_checked, root7Node56Step1Chunk8_3_checked, root7Node56Step1Chunk8_4_checked, root7Node56Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node56Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node56Domains1 (.output 26) = true := by decide
def root7Node57Domains0 : Domains 61 State := restrict root7Node55Domains3 49 (8,1)
def root7Node57Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 49 => some [(8,1)]
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
theorem root7Node57Domains0_fast_eq : root7Node57Domains0 = expandDomains root7Node57Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node57Domains0 v = expandDomains root7Node57Domains0Fast v from by decide) v
def root7Node57Domains1 (v : Fin 61) : List State :=
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
  | 49 => [(8,1)]
  | 50 => [(1,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4)]
def root7Node57Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 49 => some [(8,1)]
  | 50 => some [(1,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4)]
theorem root7Node57Domains1_fast_eq : root7Node57Domains1 = expandDomains root7Node57Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node57Domains1 v = expandDomains root7Node57Domains1Fast v from by decide) v
theorem root7Node57Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1_checked :
    checkReplacement table39 root7Node57Domains0 root7Node57Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node57Step1Chunk0_0_checked, root7Node57Step1Chunk0_1_checked, root7Node57Step1Chunk0_2_checked, root7Node57Step1Chunk0_3_checked, root7Node57Step1Chunk0_4_checked, root7Node57Step1Chunk0_5_checked, root7Node57Step1Chunk1_0_checked, root7Node57Step1Chunk1_1_checked, root7Node57Step1Chunk1_2_checked, root7Node57Step1Chunk1_3_checked, root7Node57Step1Chunk1_4_checked, root7Node57Step1Chunk1_5_checked, root7Node57Step1Chunk2_0_checked, root7Node57Step1Chunk2_1_checked, root7Node57Step1Chunk2_2_checked, root7Node57Step1Chunk2_3_checked, root7Node57Step1Chunk2_4_checked, root7Node57Step1Chunk2_5_checked, root7Node57Step1Chunk3_0_checked, root7Node57Step1Chunk3_1_checked, root7Node57Step1Chunk3_2_checked, root7Node57Step1Chunk3_3_checked, root7Node57Step1Chunk3_4_checked, root7Node57Step1Chunk3_5_checked, root7Node57Step1Chunk4_0_checked, root7Node57Step1Chunk4_1_checked, root7Node57Step1Chunk4_2_checked, root7Node57Step1Chunk4_3_checked, root7Node57Step1Chunk4_4_checked, root7Node57Step1Chunk4_5_checked, root7Node57Step1Chunk5_0_checked, root7Node57Step1Chunk5_1_checked, root7Node57Step1Chunk5_2_checked, root7Node57Step1Chunk5_3_checked, root7Node57Step1Chunk5_4_checked, root7Node57Step1Chunk5_5_checked, root7Node57Step1Chunk6_0_checked, root7Node57Step1Chunk6_1_checked, root7Node57Step1Chunk6_2_checked, root7Node57Step1Chunk6_3_checked, root7Node57Step1Chunk6_4_checked, root7Node57Step1Chunk6_5_checked, root7Node57Step1Chunk7_0_checked, root7Node57Step1Chunk7_1_checked, root7Node57Step1Chunk7_2_checked, root7Node57Step1Chunk7_3_checked, root7Node57Step1Chunk7_4_checked, root7Node57Step1Chunk7_5_checked, root7Node57Step1Chunk8_0_checked, root7Node57Step1Chunk8_1_checked, root7Node57Step1Chunk8_2_checked, root7Node57Step1Chunk8_3_checked, root7Node57Step1Chunk8_4_checked, root7Node57Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node57Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node57Domains1 (.output 27) = true := by decide
def root7Node58Domains0 : Domains 61 State := restrict root7Node48Domains1 26 (7,3)
def root7Node58Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,3)]
  | 35 => some [(0,4),(6,2)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(0,0),(1,4),(6,4),(7,4)]
  | 43 => some [(2,1),(2,3),(2,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(1,5),(4,1),(7,5),(8,1)]
  | 50 => some [(1,2),(3,2),(7,2)]
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
theorem root7Node58Domains0_fast_eq : root7Node58Domains0 = expandDomains root7Node58Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node58Domains0 v = expandDomains root7Node58Domains0Fast v from by decide) v
def root7Node58Domains1 (v : Fin 61) : List State :=
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
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(3,0),(7,0)]
  | 34 => [(2,3),(2,5),(4,3)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(4,4),(7,2)]
  | 42 => [(0,0),(1,4),(6,4),(7,4)]
  | 43 => [(2,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1),(7,1)]
  | 49 => [(1,5),(4,1),(7,5),(8,1)]
  | 50 => [(3,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(5,0),(8,0)]
  | 55 => [(4,5),(7,3),(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0),(1,4),(6,4)]
def root7Node58Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,3)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(0,0),(1,4),(6,4),(7,4)]
  | 43 => some [(2,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(1,5),(4,1),(7,5),(8,1)]
  | 50 => some [(3,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0),(1,4),(6,4)]
theorem root7Node58Domains1_fast_eq : root7Node58Domains1 = expandDomains root7Node58Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node58Domains1 v = expandDomains root7Node58Domains1Fast v from by decide) v
theorem root7Node58Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root7Node58Domains0 root7Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains0 root7Node58Domains1
    root7Node58Domains0Fast root7Node58Domains1Fast
    root7Node58Domains0_fast_eq root7Node58Domains1_fast_eq (by decide)
theorem root7Node58Step1_checked :
    checkReplacement table29 root7Node58Domains0 root7Node58Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node58Step1Chunk0_0_checked, root7Node58Step1Chunk0_1_checked, root7Node58Step1Chunk0_2_checked, root7Node58Step1Chunk0_3_checked, root7Node58Step1Chunk0_4_checked, root7Node58Step1Chunk0_5_checked, root7Node58Step1Chunk1_0_checked, root7Node58Step1Chunk1_1_checked, root7Node58Step1Chunk1_2_checked, root7Node58Step1Chunk1_3_checked, root7Node58Step1Chunk1_4_checked, root7Node58Step1Chunk1_5_checked, root7Node58Step1Chunk2_0_checked, root7Node58Step1Chunk2_1_checked, root7Node58Step1Chunk2_2_checked, root7Node58Step1Chunk2_3_checked, root7Node58Step1Chunk2_4_checked, root7Node58Step1Chunk2_5_checked, root7Node58Step1Chunk3_0_checked, root7Node58Step1Chunk3_1_checked, root7Node58Step1Chunk3_2_checked, root7Node58Step1Chunk3_3_checked, root7Node58Step1Chunk3_4_checked, root7Node58Step1Chunk3_5_checked, root7Node58Step1Chunk4_0_checked, root7Node58Step1Chunk4_1_checked, root7Node58Step1Chunk4_2_checked, root7Node58Step1Chunk4_3_checked, root7Node58Step1Chunk4_4_checked, root7Node58Step1Chunk4_5_checked, root7Node58Step1Chunk5_0_checked, root7Node58Step1Chunk5_1_checked, root7Node58Step1Chunk5_2_checked, root7Node58Step1Chunk5_3_checked, root7Node58Step1Chunk5_4_checked, root7Node58Step1Chunk5_5_checked, root7Node58Step1Chunk6_0_checked, root7Node58Step1Chunk6_1_checked, root7Node58Step1Chunk6_2_checked, root7Node58Step1Chunk6_3_checked, root7Node58Step1Chunk6_4_checked, root7Node58Step1Chunk6_5_checked, root7Node58Step1Chunk7_0_checked, root7Node58Step1Chunk7_1_checked, root7Node58Step1Chunk7_2_checked, root7Node58Step1Chunk7_3_checked, root7Node58Step1Chunk7_4_checked, root7Node58Step1Chunk7_5_checked, root7Node58Step1Chunk8_0_checked, root7Node58Step1Chunk8_1_checked, root7Node58Step1Chunk8_2_checked, root7Node58Step1Chunk8_3_checked, root7Node58Step1Chunk8_4_checked, root7Node58Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node58Domains2 (v : Fin 61) : List State :=
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
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(2,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(3,2)]
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
def root7Node58Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(2,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(3,2)]
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
theorem root7Node58Domains2_fast_eq : root7Node58Domains2 = expandDomains root7Node58Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node58Domains2 v = expandDomains root7Node58Domains2Fast v from by decide) v
theorem root7Node58Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root7Node58Domains1 root7Node58Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node58Domains1 root7Node58Domains2
    root7Node58Domains1Fast root7Node58Domains2Fast
    root7Node58Domains1_fast_eq root7Node58Domains2_fast_eq (by decide)
theorem root7Node58Step2_checked :
    checkReplacement table40 root7Node58Domains1 root7Node58Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node58Step2Chunk0_0_checked, root7Node58Step2Chunk0_1_checked, root7Node58Step2Chunk0_2_checked, root7Node58Step2Chunk0_3_checked, root7Node58Step2Chunk0_4_checked, root7Node58Step2Chunk0_5_checked, root7Node58Step2Chunk1_0_checked, root7Node58Step2Chunk1_1_checked, root7Node58Step2Chunk1_2_checked, root7Node58Step2Chunk1_3_checked, root7Node58Step2Chunk1_4_checked, root7Node58Step2Chunk1_5_checked, root7Node58Step2Chunk2_0_checked, root7Node58Step2Chunk2_1_checked, root7Node58Step2Chunk2_2_checked, root7Node58Step2Chunk2_3_checked, root7Node58Step2Chunk2_4_checked, root7Node58Step2Chunk2_5_checked, root7Node58Step2Chunk3_0_checked, root7Node58Step2Chunk3_1_checked, root7Node58Step2Chunk3_2_checked, root7Node58Step2Chunk3_3_checked, root7Node58Step2Chunk3_4_checked, root7Node58Step2Chunk3_5_checked, root7Node58Step2Chunk4_0_checked, root7Node58Step2Chunk4_1_checked, root7Node58Step2Chunk4_2_checked, root7Node58Step2Chunk4_3_checked, root7Node58Step2Chunk4_4_checked, root7Node58Step2Chunk4_5_checked, root7Node58Step2Chunk5_0_checked, root7Node58Step2Chunk5_1_checked, root7Node58Step2Chunk5_2_checked, root7Node58Step2Chunk5_3_checked, root7Node58Step2Chunk5_4_checked, root7Node58Step2Chunk5_5_checked, root7Node58Step2Chunk6_0_checked, root7Node58Step2Chunk6_1_checked, root7Node58Step2Chunk6_2_checked, root7Node58Step2Chunk6_3_checked, root7Node58Step2Chunk6_4_checked, root7Node58Step2Chunk6_5_checked, root7Node58Step2Chunk7_0_checked, root7Node58Step2Chunk7_1_checked, root7Node58Step2Chunk7_2_checked, root7Node58Step2Chunk7_3_checked, root7Node58Step2Chunk7_4_checked, root7Node58Step2Chunk7_5_checked, root7Node58Step2Chunk8_0_checked, root7Node58Step2Chunk8_1_checked, root7Node58Step2Chunk8_2_checked, root7Node58Step2Chunk8_3_checked, root7Node58Step2Chunk8_4_checked, root7Node58Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node59Domains0 : Domains 61 State := restrict root7Node58Domains2 49 (4,1)
def root7Node59Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(2,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(3,2)]
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
theorem root7Node59Domains0_fast_eq : root7Node59Domains0 = expandDomains root7Node59Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node59Domains0 v = expandDomains root7Node59Domains0Fast v from by decide) v
def root7Node59Domains1 (v : Fin 61) : List State :=
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
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(2,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(3,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(6,4)]
def root7Node59Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(2,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(3,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(6,4)]
theorem root7Node59Domains1_fast_eq : root7Node59Domains1 = expandDomains root7Node59Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node59Domains1 v = expandDomains root7Node59Domains1Fast v from by decide) v
theorem root7Node59Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node59Domains0 root7Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node59Domains0 root7Node59Domains1
    root7Node59Domains0Fast root7Node59Domains1Fast
    root7Node59Domains0_fast_eq root7Node59Domains1_fast_eq (by decide)
theorem root7Node59Step1_checked :
    checkReplacement table39 root7Node59Domains0 root7Node59Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node59Step1Chunk0_0_checked, root7Node59Step1Chunk0_1_checked, root7Node59Step1Chunk0_2_checked, root7Node59Step1Chunk0_3_checked, root7Node59Step1Chunk0_4_checked, root7Node59Step1Chunk0_5_checked, root7Node59Step1Chunk1_0_checked, root7Node59Step1Chunk1_1_checked, root7Node59Step1Chunk1_2_checked, root7Node59Step1Chunk1_3_checked, root7Node59Step1Chunk1_4_checked, root7Node59Step1Chunk1_5_checked, root7Node59Step1Chunk2_0_checked, root7Node59Step1Chunk2_1_checked, root7Node59Step1Chunk2_2_checked, root7Node59Step1Chunk2_3_checked, root7Node59Step1Chunk2_4_checked, root7Node59Step1Chunk2_5_checked, root7Node59Step1Chunk3_0_checked, root7Node59Step1Chunk3_1_checked, root7Node59Step1Chunk3_2_checked, root7Node59Step1Chunk3_3_checked, root7Node59Step1Chunk3_4_checked, root7Node59Step1Chunk3_5_checked, root7Node59Step1Chunk4_0_checked, root7Node59Step1Chunk4_1_checked, root7Node59Step1Chunk4_2_checked, root7Node59Step1Chunk4_3_checked, root7Node59Step1Chunk4_4_checked, root7Node59Step1Chunk4_5_checked, root7Node59Step1Chunk5_0_checked, root7Node59Step1Chunk5_1_checked, root7Node59Step1Chunk5_2_checked, root7Node59Step1Chunk5_3_checked, root7Node59Step1Chunk5_4_checked, root7Node59Step1Chunk5_5_checked, root7Node59Step1Chunk6_0_checked, root7Node59Step1Chunk6_1_checked, root7Node59Step1Chunk6_2_checked, root7Node59Step1Chunk6_3_checked, root7Node59Step1Chunk6_4_checked, root7Node59Step1Chunk6_5_checked, root7Node59Step1Chunk7_0_checked, root7Node59Step1Chunk7_1_checked, root7Node59Step1Chunk7_2_checked, root7Node59Step1Chunk7_3_checked, root7Node59Step1Chunk7_4_checked, root7Node59Step1Chunk7_5_checked, root7Node59Step1Chunk8_0_checked, root7Node59Step1Chunk8_1_checked, root7Node59Step1Chunk8_2_checked, root7Node59Step1Chunk8_3_checked, root7Node59Step1Chunk8_4_checked, root7Node59Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node59Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node59Domains1 (.output 28) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
