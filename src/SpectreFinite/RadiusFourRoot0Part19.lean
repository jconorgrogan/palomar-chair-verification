module

public import SpectreFinite.RadiusFourRoot0Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node55Domains0 : Domains 61 State := restrict root0Node54Domains2 54 (1,3)
def root0Node55Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node55Domains0_fast_eq : root0Node55Domains0 = expandDomains root0Node55Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node55Domains0 v = expandDomains root0Node55Domains0Fast v from by decide) v
def root0Node55Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(7,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(8,1)]
  | 59 => [(6,5)]
  | _ => [(0,4)]
def root0Node55Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(8,1)]
  | 59 => some [(6,5)]
  | _ => some [(0,4)]
theorem root0Node55Domains1_fast_eq : root0Node55Domains1 = expandDomains root0Node55Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node55Domains1 v = expandDomains root0Node55Domains1Fast v from by decide) v
theorem root0Node55Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node55Domains0 root0Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node55Domains0 root0Node55Domains1
    root0Node55Domains0Fast root0Node55Domains1Fast
    root0Node55Domains0_fast_eq root0Node55Domains1_fast_eq (by decide)
theorem root0Node55Step1_checked :
    checkReplacement table39 root0Node55Domains0 root0Node55Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node55Step1Chunk0_0_checked, root0Node55Step1Chunk0_1_checked, root0Node55Step1Chunk0_2_checked, root0Node55Step1Chunk0_3_checked, root0Node55Step1Chunk0_4_checked, root0Node55Step1Chunk0_5_checked, root0Node55Step1Chunk1_0_checked, root0Node55Step1Chunk1_1_checked, root0Node55Step1Chunk1_2_checked, root0Node55Step1Chunk1_3_checked, root0Node55Step1Chunk1_4_checked, root0Node55Step1Chunk1_5_checked, root0Node55Step1Chunk2_0_checked, root0Node55Step1Chunk2_1_checked, root0Node55Step1Chunk2_2_checked, root0Node55Step1Chunk2_3_checked, root0Node55Step1Chunk2_4_checked, root0Node55Step1Chunk2_5_checked, root0Node55Step1Chunk3_0_checked, root0Node55Step1Chunk3_1_checked, root0Node55Step1Chunk3_2_checked, root0Node55Step1Chunk3_3_checked, root0Node55Step1Chunk3_4_checked, root0Node55Step1Chunk3_5_checked, root0Node55Step1Chunk4_0_checked, root0Node55Step1Chunk4_1_checked, root0Node55Step1Chunk4_2_checked, root0Node55Step1Chunk4_3_checked, root0Node55Step1Chunk4_4_checked, root0Node55Step1Chunk4_5_checked, root0Node55Step1Chunk5_0_checked, root0Node55Step1Chunk5_1_checked, root0Node55Step1Chunk5_2_checked, root0Node55Step1Chunk5_3_checked, root0Node55Step1Chunk5_4_checked, root0Node55Step1Chunk5_5_checked, root0Node55Step1Chunk6_0_checked, root0Node55Step1Chunk6_1_checked, root0Node55Step1Chunk6_2_checked, root0Node55Step1Chunk6_3_checked, root0Node55Step1Chunk6_4_checked, root0Node55Step1Chunk6_5_checked, root0Node55Step1Chunk7_0_checked, root0Node55Step1Chunk7_1_checked, root0Node55Step1Chunk7_2_checked, root0Node55Step1Chunk7_3_checked, root0Node55Step1Chunk7_4_checked, root0Node55Step1Chunk7_5_checked, root0Node55Step1Chunk8_0_checked, root0Node55Step1Chunk8_1_checked, root0Node55Step1Chunk8_2_checked, root0Node55Step1Chunk8_3_checked, root0Node55Step1Chunk8_4_checked, root0Node55Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node55Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node55Domains1 (.output 26) = true := by decide
def root0Node56Domains0 : Domains 61 State := restrict root0Node54Domains2 54 (6,3)
def root0Node56Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node56Domains0_fast_eq : root0Node56Domains0 = expandDomains root0Node56Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node56Domains0 v = expandDomains root0Node56Domains0Fast v from by decide) v
def root0Node56Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(1,5)]
  | 3 => [(6,1)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,0)]
  | 9 => [(7,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(3,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(7,4)]
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
def root0Node56Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(1,5)]
  | 3 => some [(6,1)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,0)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(3,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(7,4)]
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
theorem root0Node56Domains1_fast_eq : root0Node56Domains1 = expandDomains root0Node56Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node56Domains1 v = expandDomains root0Node56Domains1Fast v from by decide) v
theorem root0Node56Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node56Domains0 root0Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node56Domains0 root0Node56Domains1
    root0Node56Domains0Fast root0Node56Domains1Fast
    root0Node56Domains0_fast_eq root0Node56Domains1_fast_eq (by decide)
theorem root0Node56Step1_checked :
    checkReplacement table39 root0Node56Domains0 root0Node56Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node56Step1Chunk0_0_checked, root0Node56Step1Chunk0_1_checked, root0Node56Step1Chunk0_2_checked, root0Node56Step1Chunk0_3_checked, root0Node56Step1Chunk0_4_checked, root0Node56Step1Chunk0_5_checked, root0Node56Step1Chunk1_0_checked, root0Node56Step1Chunk1_1_checked, root0Node56Step1Chunk1_2_checked, root0Node56Step1Chunk1_3_checked, root0Node56Step1Chunk1_4_checked, root0Node56Step1Chunk1_5_checked, root0Node56Step1Chunk2_0_checked, root0Node56Step1Chunk2_1_checked, root0Node56Step1Chunk2_2_checked, root0Node56Step1Chunk2_3_checked, root0Node56Step1Chunk2_4_checked, root0Node56Step1Chunk2_5_checked, root0Node56Step1Chunk3_0_checked, root0Node56Step1Chunk3_1_checked, root0Node56Step1Chunk3_2_checked, root0Node56Step1Chunk3_3_checked, root0Node56Step1Chunk3_4_checked, root0Node56Step1Chunk3_5_checked, root0Node56Step1Chunk4_0_checked, root0Node56Step1Chunk4_1_checked, root0Node56Step1Chunk4_2_checked, root0Node56Step1Chunk4_3_checked, root0Node56Step1Chunk4_4_checked, root0Node56Step1Chunk4_5_checked, root0Node56Step1Chunk5_0_checked, root0Node56Step1Chunk5_1_checked, root0Node56Step1Chunk5_2_checked, root0Node56Step1Chunk5_3_checked, root0Node56Step1Chunk5_4_checked, root0Node56Step1Chunk5_5_checked, root0Node56Step1Chunk6_0_checked, root0Node56Step1Chunk6_1_checked, root0Node56Step1Chunk6_2_checked, root0Node56Step1Chunk6_3_checked, root0Node56Step1Chunk6_4_checked, root0Node56Step1Chunk6_5_checked, root0Node56Step1Chunk7_0_checked, root0Node56Step1Chunk7_1_checked, root0Node56Step1Chunk7_2_checked, root0Node56Step1Chunk7_3_checked, root0Node56Step1Chunk7_4_checked, root0Node56Step1Chunk7_5_checked, root0Node56Step1Chunk8_0_checked, root0Node56Step1Chunk8_1_checked, root0Node56Step1Chunk8_2_checked, root0Node56Step1Chunk8_3_checked, root0Node56Step1Chunk8_4_checked, root0Node56Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node56Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node56Domains1 (.output 27) = true := by decide
def root0Node57Domains0 : Domains 61 State := restrict root0Node25Domains1 1 (8,3)
def root0Node57Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node57Domains0_fast_eq : root0Node57Domains0 = expandDomains root0Node57Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node57Domains0 v = expandDomains root0Node57Domains0Fast v from by decide) v
def root0Node57Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(2,1),(2,5),(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(5,4),(8,4)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3),(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(0,1),(6,5)]
  | 42 => [(0,4),(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node57Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node57Domains1_fast_eq : root0Node57Domains1 = expandDomains root0Node57Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node57Domains1 v = expandDomains root0Node57Domains1Fast v from by decide) v
theorem root0Node57Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root0Node57Domains0 root0Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains0 root0Node57Domains1
    root0Node57Domains0Fast root0Node57Domains1Fast
    root0Node57Domains0_fast_eq root0Node57Domains1_fast_eq (by decide)
theorem root0Node57Step1_checked :
    checkReplacement table21 root0Node57Domains0 root0Node57Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node57Step1Chunk0_0_checked, root0Node57Step1Chunk0_1_checked, root0Node57Step1Chunk0_2_checked, root0Node57Step1Chunk0_3_checked, root0Node57Step1Chunk0_4_checked, root0Node57Step1Chunk0_5_checked, root0Node57Step1Chunk1_0_checked, root0Node57Step1Chunk1_1_checked, root0Node57Step1Chunk1_2_checked, root0Node57Step1Chunk1_3_checked, root0Node57Step1Chunk1_4_checked, root0Node57Step1Chunk1_5_checked, root0Node57Step1Chunk2_0_checked, root0Node57Step1Chunk2_1_checked, root0Node57Step1Chunk2_2_checked, root0Node57Step1Chunk2_3_checked, root0Node57Step1Chunk2_4_checked, root0Node57Step1Chunk2_5_checked, root0Node57Step1Chunk3_0_checked, root0Node57Step1Chunk3_1_checked, root0Node57Step1Chunk3_2_checked, root0Node57Step1Chunk3_3_checked, root0Node57Step1Chunk3_4_checked, root0Node57Step1Chunk3_5_checked, root0Node57Step1Chunk4_0_checked, root0Node57Step1Chunk4_1_checked, root0Node57Step1Chunk4_2_checked, root0Node57Step1Chunk4_3_checked, root0Node57Step1Chunk4_4_checked, root0Node57Step1Chunk4_5_checked, root0Node57Step1Chunk5_0_checked, root0Node57Step1Chunk5_1_checked, root0Node57Step1Chunk5_2_checked, root0Node57Step1Chunk5_3_checked, root0Node57Step1Chunk5_4_checked, root0Node57Step1Chunk5_5_checked, root0Node57Step1Chunk6_0_checked, root0Node57Step1Chunk6_1_checked, root0Node57Step1Chunk6_2_checked, root0Node57Step1Chunk6_3_checked, root0Node57Step1Chunk6_4_checked, root0Node57Step1Chunk6_5_checked, root0Node57Step1Chunk7_0_checked, root0Node57Step1Chunk7_1_checked, root0Node57Step1Chunk7_2_checked, root0Node57Step1Chunk7_3_checked, root0Node57Step1Chunk7_4_checked, root0Node57Step1Chunk7_5_checked, root0Node57Step1Chunk8_0_checked, root0Node57Step1Chunk8_1_checked, root0Node57Step1Chunk8_2_checked, root0Node57Step1Chunk8_3_checked, root0Node57Step1Chunk8_4_checked, root0Node57Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node57Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(2,1),(2,5),(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(5,4),(8,4)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3),(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4),(6,2)]
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
def root0Node57Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4),(6,2)]
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
theorem root0Node57Domains2_fast_eq : root0Node57Domains2 = expandDomains root0Node57Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node57Domains2 v = expandDomains root0Node57Domains2Fast v from by decide) v
theorem root0Node57Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root0Node57Domains1 root0Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains1 root0Node57Domains2
    root0Node57Domains1Fast root0Node57Domains2Fast
    root0Node57Domains1_fast_eq root0Node57Domains2_fast_eq (by decide)
theorem root0Node57Step2_checked :
    checkReplacement table46 root0Node57Domains1 root0Node57Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node57Step2Chunk0_0_checked, root0Node57Step2Chunk0_1_checked, root0Node57Step2Chunk0_2_checked, root0Node57Step2Chunk0_3_checked, root0Node57Step2Chunk0_4_checked, root0Node57Step2Chunk0_5_checked, root0Node57Step2Chunk1_0_checked, root0Node57Step2Chunk1_1_checked, root0Node57Step2Chunk1_2_checked, root0Node57Step2Chunk1_3_checked, root0Node57Step2Chunk1_4_checked, root0Node57Step2Chunk1_5_checked, root0Node57Step2Chunk2_0_checked, root0Node57Step2Chunk2_1_checked, root0Node57Step2Chunk2_2_checked, root0Node57Step2Chunk2_3_checked, root0Node57Step2Chunk2_4_checked, root0Node57Step2Chunk2_5_checked, root0Node57Step2Chunk3_0_checked, root0Node57Step2Chunk3_1_checked, root0Node57Step2Chunk3_2_checked, root0Node57Step2Chunk3_3_checked, root0Node57Step2Chunk3_4_checked, root0Node57Step2Chunk3_5_checked, root0Node57Step2Chunk4_0_checked, root0Node57Step2Chunk4_1_checked, root0Node57Step2Chunk4_2_checked, root0Node57Step2Chunk4_3_checked, root0Node57Step2Chunk4_4_checked, root0Node57Step2Chunk4_5_checked, root0Node57Step2Chunk5_0_checked, root0Node57Step2Chunk5_1_checked, root0Node57Step2Chunk5_2_checked, root0Node57Step2Chunk5_3_checked, root0Node57Step2Chunk5_4_checked, root0Node57Step2Chunk5_5_checked, root0Node57Step2Chunk6_0_checked, root0Node57Step2Chunk6_1_checked, root0Node57Step2Chunk6_2_checked, root0Node57Step2Chunk6_3_checked, root0Node57Step2Chunk6_4_checked, root0Node57Step2Chunk6_5_checked, root0Node57Step2Chunk7_0_checked, root0Node57Step2Chunk7_1_checked, root0Node57Step2Chunk7_2_checked, root0Node57Step2Chunk7_3_checked, root0Node57Step2Chunk7_4_checked, root0Node57Step2Chunk7_5_checked, root0Node57Step2Chunk8_0_checked, root0Node57Step2Chunk8_1_checked, root0Node57Step2Chunk8_2_checked, root0Node57Step2Chunk8_3_checked, root0Node57Step2Chunk8_4_checked, root0Node57Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node57Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(2,1),(2,5)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(7,2)]
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
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5),(8,5)]
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
def root0Node57Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(2,1),(2,5)]
  | 5 => some [(4,4)]
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
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5),(8,5)]
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
theorem root0Node57Domains3_fast_eq : root0Node57Domains3 = expandDomains root0Node57Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node57Domains3 v = expandDomains root0Node57Domains3Fast v from by decide) v
theorem root0Node57Step3Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root0Node57Domains2 root0Node57Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node57Domains2 root0Node57Domains3
    root0Node57Domains2Fast root0Node57Domains3Fast
    root0Node57Domains2_fast_eq root0Node57Domains3_fast_eq (by decide)
theorem root0Node57Step3_checked :
    checkReplacement table16 root0Node57Domains2 root0Node57Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node57Step3Chunk0_0_checked, root0Node57Step3Chunk0_1_checked, root0Node57Step3Chunk0_2_checked, root0Node57Step3Chunk0_3_checked, root0Node57Step3Chunk0_4_checked, root0Node57Step3Chunk0_5_checked, root0Node57Step3Chunk1_0_checked, root0Node57Step3Chunk1_1_checked, root0Node57Step3Chunk1_2_checked, root0Node57Step3Chunk1_3_checked, root0Node57Step3Chunk1_4_checked, root0Node57Step3Chunk1_5_checked, root0Node57Step3Chunk2_0_checked, root0Node57Step3Chunk2_1_checked, root0Node57Step3Chunk2_2_checked, root0Node57Step3Chunk2_3_checked, root0Node57Step3Chunk2_4_checked, root0Node57Step3Chunk2_5_checked, root0Node57Step3Chunk3_0_checked, root0Node57Step3Chunk3_1_checked, root0Node57Step3Chunk3_2_checked, root0Node57Step3Chunk3_3_checked, root0Node57Step3Chunk3_4_checked, root0Node57Step3Chunk3_5_checked, root0Node57Step3Chunk4_0_checked, root0Node57Step3Chunk4_1_checked, root0Node57Step3Chunk4_2_checked, root0Node57Step3Chunk4_3_checked, root0Node57Step3Chunk4_4_checked, root0Node57Step3Chunk4_5_checked, root0Node57Step3Chunk5_0_checked, root0Node57Step3Chunk5_1_checked, root0Node57Step3Chunk5_2_checked, root0Node57Step3Chunk5_3_checked, root0Node57Step3Chunk5_4_checked, root0Node57Step3Chunk5_5_checked, root0Node57Step3Chunk6_0_checked, root0Node57Step3Chunk6_1_checked, root0Node57Step3Chunk6_2_checked, root0Node57Step3Chunk6_3_checked, root0Node57Step3Chunk6_4_checked, root0Node57Step3Chunk6_5_checked, root0Node57Step3Chunk7_0_checked, root0Node57Step3Chunk7_1_checked, root0Node57Step3Chunk7_2_checked, root0Node57Step3Chunk7_3_checked, root0Node57Step3Chunk7_4_checked, root0Node57Step3Chunk7_5_checked, root0Node57Step3Chunk8_0_checked, root0Node57Step3Chunk8_1_checked, root0Node57Step3Chunk8_2_checked, root0Node57Step3Chunk8_3_checked, root0Node57Step3Chunk8_4_checked, root0Node57Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
