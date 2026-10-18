module

public import SpectreFinite.RadiusFourRoot5Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable5
public import SpectreFinite.RadiusFourTable7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node3Domains0 : Domains 61 State := restrict root5Node2Domains2 6 (4,0)
def root5Node3Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1),(5,1),(8,1)]
  | 3 => some [(0,1),(0,2),(6,5)]
  | 4 => some [(0,4),(1,1),(6,2)]
  | 5 => some [(1,2),(3,2),(5,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node3Domains0_fast_eq : root5Node3Domains0 = expandDomains root5Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node3Domains0 v = expandDomains root5Node3Domains0Fast v from by decide) v
def root5Node3Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(1,2),(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(0,3),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(5,3),(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node3Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(1,2),(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node3Domains1_fast_eq : root5Node3Domains1 = expandDomains root5Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node3Domains1 v = expandDomains root5Node3Domains1Fast v from by decide) v
theorem root5Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root5Node3Domains0 root5Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node3Domains0 root5Node3Domains1
    root5Node3Domains0Fast root5Node3Domains1Fast
    root5Node3Domains0_fast_eq root5Node3Domains1_fast_eq (by decide)
theorem root5Node3Step1_checked :
    checkReplacement table14 root5Node3Domains0 root5Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node3Step1Chunk0_0_checked, root5Node3Step1Chunk0_1_checked, root5Node3Step1Chunk0_2_checked, root5Node3Step1Chunk0_3_checked, root5Node3Step1Chunk0_4_checked, root5Node3Step1Chunk0_5_checked, root5Node3Step1Chunk1_0_checked, root5Node3Step1Chunk1_1_checked, root5Node3Step1Chunk1_2_checked, root5Node3Step1Chunk1_3_checked, root5Node3Step1Chunk1_4_checked, root5Node3Step1Chunk1_5_checked, root5Node3Step1Chunk2_0_checked, root5Node3Step1Chunk2_1_checked, root5Node3Step1Chunk2_2_checked, root5Node3Step1Chunk2_3_checked, root5Node3Step1Chunk2_4_checked, root5Node3Step1Chunk2_5_checked, root5Node3Step1Chunk3_0_checked, root5Node3Step1Chunk3_1_checked, root5Node3Step1Chunk3_2_checked, root5Node3Step1Chunk3_3_checked, root5Node3Step1Chunk3_4_checked, root5Node3Step1Chunk3_5_checked, root5Node3Step1Chunk4_0_checked, root5Node3Step1Chunk4_1_checked, root5Node3Step1Chunk4_2_checked, root5Node3Step1Chunk4_3_checked, root5Node3Step1Chunk4_4_checked, root5Node3Step1Chunk4_5_checked, root5Node3Step1Chunk5_0_checked, root5Node3Step1Chunk5_1_checked, root5Node3Step1Chunk5_2_checked, root5Node3Step1Chunk5_3_checked, root5Node3Step1Chunk5_4_checked, root5Node3Step1Chunk5_5_checked, root5Node3Step1Chunk6_0_checked, root5Node3Step1Chunk6_1_checked, root5Node3Step1Chunk6_2_checked, root5Node3Step1Chunk6_3_checked, root5Node3Step1Chunk6_4_checked, root5Node3Step1Chunk6_5_checked, root5Node3Step1Chunk7_0_checked, root5Node3Step1Chunk7_1_checked, root5Node3Step1Chunk7_2_checked, root5Node3Step1Chunk7_3_checked, root5Node3Step1Chunk7_4_checked, root5Node3Step1Chunk7_5_checked, root5Node3Step1Chunk8_0_checked, root5Node3Step1Chunk8_1_checked, root5Node3Step1Chunk8_2_checked, root5Node3Step1Chunk8_3_checked, root5Node3Step1Chunk8_4_checked, root5Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node4Domains0 : Domains 61 State := restrict root5Node3Domains1 5 (1,2)
def root5Node4Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(1,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node4Domains0_fast_eq : root5Node4Domains0 = expandDomains root5Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node4Domains0 v = expandDomains root5Node4Domains0Fast v from by decide) v
def root5Node4Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(1,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(0,3)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,2)]
  | 19 => [(5,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(1,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node4Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(1,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(0,3)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,2)]
  | 19 => some [(5,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node4Domains1_fast_eq : root5Node4Domains1 = expandDomains root5Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node4Domains1 v = expandDomains root5Node4Domains1Fast v from by decide) v
theorem root5Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root5Node4Domains0 root5Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node4Domains0 root5Node4Domains1
    root5Node4Domains0Fast root5Node4Domains1Fast
    root5Node4Domains0_fast_eq root5Node4Domains1_fast_eq (by decide)
theorem root5Node4Step1_checked :
    checkReplacement table5 root5Node4Domains0 root5Node4Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node4Step1Chunk0_0_checked, root5Node4Step1Chunk0_1_checked, root5Node4Step1Chunk0_2_checked, root5Node4Step1Chunk0_3_checked, root5Node4Step1Chunk0_4_checked, root5Node4Step1Chunk0_5_checked, root5Node4Step1Chunk1_0_checked, root5Node4Step1Chunk1_1_checked, root5Node4Step1Chunk1_2_checked, root5Node4Step1Chunk1_3_checked, root5Node4Step1Chunk1_4_checked, root5Node4Step1Chunk1_5_checked, root5Node4Step1Chunk2_0_checked, root5Node4Step1Chunk2_1_checked, root5Node4Step1Chunk2_2_checked, root5Node4Step1Chunk2_3_checked, root5Node4Step1Chunk2_4_checked, root5Node4Step1Chunk2_5_checked, root5Node4Step1Chunk3_0_checked, root5Node4Step1Chunk3_1_checked, root5Node4Step1Chunk3_2_checked, root5Node4Step1Chunk3_3_checked, root5Node4Step1Chunk3_4_checked, root5Node4Step1Chunk3_5_checked, root5Node4Step1Chunk4_0_checked, root5Node4Step1Chunk4_1_checked, root5Node4Step1Chunk4_2_checked, root5Node4Step1Chunk4_3_checked, root5Node4Step1Chunk4_4_checked, root5Node4Step1Chunk4_5_checked, root5Node4Step1Chunk5_0_checked, root5Node4Step1Chunk5_1_checked, root5Node4Step1Chunk5_2_checked, root5Node4Step1Chunk5_3_checked, root5Node4Step1Chunk5_4_checked, root5Node4Step1Chunk5_5_checked, root5Node4Step1Chunk6_0_checked, root5Node4Step1Chunk6_1_checked, root5Node4Step1Chunk6_2_checked, root5Node4Step1Chunk6_3_checked, root5Node4Step1Chunk6_4_checked, root5Node4Step1Chunk6_5_checked, root5Node4Step1Chunk7_0_checked, root5Node4Step1Chunk7_1_checked, root5Node4Step1Chunk7_2_checked, root5Node4Step1Chunk7_3_checked, root5Node4Step1Chunk7_4_checked, root5Node4Step1Chunk7_5_checked, root5Node4Step1Chunk8_0_checked, root5Node4Step1Chunk8_1_checked, root5Node4Step1Chunk8_2_checked, root5Node4Step1Chunk8_3_checked, root5Node4Step1Chunk8_4_checked, root5Node4Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node4Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node4Domains1 (.output 0) = true := by decide
def root5Node5Domains0 : Domains 61 State := restrict root5Node3Domains1 5 (3,2)
def root5Node5Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node5Domains0_fast_eq : root5Node5Domains0 = expandDomains root5Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node5Domains0 v = expandDomains root5Node5Domains0Fast v from by decide) v
def root5Node5Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node5Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node5Domains1_fast_eq : root5Node5Domains1 = expandDomains root5Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node5Domains1 v = expandDomains root5Node5Domains1Fast v from by decide) v
theorem root5Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root5Node5Domains0 root5Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node5Domains0 root5Node5Domains1
    root5Node5Domains0Fast root5Node5Domains1Fast
    root5Node5Domains0_fast_eq root5Node5Domains1_fast_eq (by decide)
theorem root5Node5Step1_checked :
    checkReplacement table5 root5Node5Domains0 root5Node5Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node5Step1Chunk0_0_checked, root5Node5Step1Chunk0_1_checked, root5Node5Step1Chunk0_2_checked, root5Node5Step1Chunk0_3_checked, root5Node5Step1Chunk0_4_checked, root5Node5Step1Chunk0_5_checked, root5Node5Step1Chunk1_0_checked, root5Node5Step1Chunk1_1_checked, root5Node5Step1Chunk1_2_checked, root5Node5Step1Chunk1_3_checked, root5Node5Step1Chunk1_4_checked, root5Node5Step1Chunk1_5_checked, root5Node5Step1Chunk2_0_checked, root5Node5Step1Chunk2_1_checked, root5Node5Step1Chunk2_2_checked, root5Node5Step1Chunk2_3_checked, root5Node5Step1Chunk2_4_checked, root5Node5Step1Chunk2_5_checked, root5Node5Step1Chunk3_0_checked, root5Node5Step1Chunk3_1_checked, root5Node5Step1Chunk3_2_checked, root5Node5Step1Chunk3_3_checked, root5Node5Step1Chunk3_4_checked, root5Node5Step1Chunk3_5_checked, root5Node5Step1Chunk4_0_checked, root5Node5Step1Chunk4_1_checked, root5Node5Step1Chunk4_2_checked, root5Node5Step1Chunk4_3_checked, root5Node5Step1Chunk4_4_checked, root5Node5Step1Chunk4_5_checked, root5Node5Step1Chunk5_0_checked, root5Node5Step1Chunk5_1_checked, root5Node5Step1Chunk5_2_checked, root5Node5Step1Chunk5_3_checked, root5Node5Step1Chunk5_4_checked, root5Node5Step1Chunk5_5_checked, root5Node5Step1Chunk6_0_checked, root5Node5Step1Chunk6_1_checked, root5Node5Step1Chunk6_2_checked, root5Node5Step1Chunk6_3_checked, root5Node5Step1Chunk6_4_checked, root5Node5Step1Chunk6_5_checked, root5Node5Step1Chunk7_0_checked, root5Node5Step1Chunk7_1_checked, root5Node5Step1Chunk7_2_checked, root5Node5Step1Chunk7_3_checked, root5Node5Step1Chunk7_4_checked, root5Node5Step1Chunk7_5_checked, root5Node5Step1Chunk8_0_checked, root5Node5Step1Chunk8_1_checked, root5Node5Step1Chunk8_2_checked, root5Node5Step1Chunk8_3_checked, root5Node5Step1Chunk8_4_checked, root5Node5Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node5Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node5Domains1 (.output 1) = true := by decide
def root5Node6Domains0 : Domains 61 State := restrict root5Node2Domains2 6 (8,0)
def root5Node6Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1),(5,1),(8,1)]
  | 3 => some [(0,1),(0,2),(6,5)]
  | 4 => some [(0,4),(1,1),(6,2)]
  | 5 => some [(1,2),(3,2),(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node6Domains0_fast_eq : root5Node6Domains0 = expandDomains root5Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node6Domains0 v = expandDomains root5Node6Domains0Fast v from by decide) v
def root5Node6Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(6,2)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0),(3,0)]
  | 10 => [(2,1),(2,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node6Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0),(3,0)]
  | 10 => some [(2,1),(2,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node6Domains1_fast_eq : root5Node6Domains1 = expandDomains root5Node6Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node6Domains1 v = expandDomains root5Node6Domains1Fast v from by decide) v
theorem root5Node6Step1Chunk0_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk0_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk0_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk0_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk0_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk0_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk1_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk1_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk1_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk1_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk1_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk1_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk2_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk2_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk2_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk2_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk2_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk2_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk3_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk3_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk3_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk3_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk3_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk3_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk4_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk4_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk4_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk4_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk4_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk4_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk5_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk5_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk5_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk5_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk5_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk5_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk6_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk6_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk6_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk6_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk6_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk6_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk7_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk7_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk7_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk7_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk7_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk7_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk8_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_0⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk8_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_1⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk8_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_2⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk8_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_3⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk8_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_4⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1Chunk8_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_5⟩
      root5Node6Domains0 root5Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains0 root5Node6Domains1
    root5Node6Domains0Fast root5Node6Domains1Fast
    root5Node6Domains0_fast_eq root5Node6Domains1_fast_eq (by decide)
theorem root5Node6Step1_checked :
    checkReplacement table7 root5Node6Domains0 root5Node6Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node6Step1Chunk0_0_checked, root5Node6Step1Chunk0_1_checked, root5Node6Step1Chunk0_2_checked, root5Node6Step1Chunk0_3_checked, root5Node6Step1Chunk0_4_checked, root5Node6Step1Chunk0_5_checked, root5Node6Step1Chunk1_0_checked, root5Node6Step1Chunk1_1_checked, root5Node6Step1Chunk1_2_checked, root5Node6Step1Chunk1_3_checked, root5Node6Step1Chunk1_4_checked, root5Node6Step1Chunk1_5_checked, root5Node6Step1Chunk2_0_checked, root5Node6Step1Chunk2_1_checked, root5Node6Step1Chunk2_2_checked, root5Node6Step1Chunk2_3_checked, root5Node6Step1Chunk2_4_checked, root5Node6Step1Chunk2_5_checked, root5Node6Step1Chunk3_0_checked, root5Node6Step1Chunk3_1_checked, root5Node6Step1Chunk3_2_checked, root5Node6Step1Chunk3_3_checked, root5Node6Step1Chunk3_4_checked, root5Node6Step1Chunk3_5_checked, root5Node6Step1Chunk4_0_checked, root5Node6Step1Chunk4_1_checked, root5Node6Step1Chunk4_2_checked, root5Node6Step1Chunk4_3_checked, root5Node6Step1Chunk4_4_checked, root5Node6Step1Chunk4_5_checked, root5Node6Step1Chunk5_0_checked, root5Node6Step1Chunk5_1_checked, root5Node6Step1Chunk5_2_checked, root5Node6Step1Chunk5_3_checked, root5Node6Step1Chunk5_4_checked, root5Node6Step1Chunk5_5_checked, root5Node6Step1Chunk6_0_checked, root5Node6Step1Chunk6_1_checked, root5Node6Step1Chunk6_2_checked, root5Node6Step1Chunk6_3_checked, root5Node6Step1Chunk6_4_checked, root5Node6Step1Chunk6_5_checked, root5Node6Step1Chunk7_0_checked, root5Node6Step1Chunk7_1_checked, root5Node6Step1Chunk7_2_checked, root5Node6Step1Chunk7_3_checked, root5Node6Step1Chunk7_4_checked, root5Node6Step1Chunk7_5_checked, root5Node6Step1Chunk8_0_checked, root5Node6Step1Chunk8_1_checked, root5Node6Step1Chunk8_2_checked, root5Node6Step1Chunk8_3_checked, root5Node6Step1Chunk8_4_checked, root5Node6Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node6Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(6,2)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0),(3,0)]
  | 10 => [(2,1),(2,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node6Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0),(3,0)]
  | 10 => some [(2,1),(2,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node6Domains2_fast_eq : root5Node6Domains2 = expandDomains root5Node6Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node6Domains2 v = expandDomains root5Node6Domains2Fast v from by decide) v
theorem root5Node6Step2Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root5Node6Domains1 root5Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node6Domains1 root5Node6Domains2
    root5Node6Domains1Fast root5Node6Domains2Fast
    root5Node6Domains1_fast_eq root5Node6Domains2_fast_eq (by decide)
theorem root5Node6Step2_checked :
    checkReplacement table5 root5Node6Domains1 root5Node6Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node6Step2Chunk0_0_checked, root5Node6Step2Chunk0_1_checked, root5Node6Step2Chunk0_2_checked, root5Node6Step2Chunk0_3_checked, root5Node6Step2Chunk0_4_checked, root5Node6Step2Chunk0_5_checked, root5Node6Step2Chunk1_0_checked, root5Node6Step2Chunk1_1_checked, root5Node6Step2Chunk1_2_checked, root5Node6Step2Chunk1_3_checked, root5Node6Step2Chunk1_4_checked, root5Node6Step2Chunk1_5_checked, root5Node6Step2Chunk2_0_checked, root5Node6Step2Chunk2_1_checked, root5Node6Step2Chunk2_2_checked, root5Node6Step2Chunk2_3_checked, root5Node6Step2Chunk2_4_checked, root5Node6Step2Chunk2_5_checked, root5Node6Step2Chunk3_0_checked, root5Node6Step2Chunk3_1_checked, root5Node6Step2Chunk3_2_checked, root5Node6Step2Chunk3_3_checked, root5Node6Step2Chunk3_4_checked, root5Node6Step2Chunk3_5_checked, root5Node6Step2Chunk4_0_checked, root5Node6Step2Chunk4_1_checked, root5Node6Step2Chunk4_2_checked, root5Node6Step2Chunk4_3_checked, root5Node6Step2Chunk4_4_checked, root5Node6Step2Chunk4_5_checked, root5Node6Step2Chunk5_0_checked, root5Node6Step2Chunk5_1_checked, root5Node6Step2Chunk5_2_checked, root5Node6Step2Chunk5_3_checked, root5Node6Step2Chunk5_4_checked, root5Node6Step2Chunk5_5_checked, root5Node6Step2Chunk6_0_checked, root5Node6Step2Chunk6_1_checked, root5Node6Step2Chunk6_2_checked, root5Node6Step2Chunk6_3_checked, root5Node6Step2Chunk6_4_checked, root5Node6Step2Chunk6_5_checked, root5Node6Step2Chunk7_0_checked, root5Node6Step2Chunk7_1_checked, root5Node6Step2Chunk7_2_checked, root5Node6Step2Chunk7_3_checked, root5Node6Step2Chunk7_4_checked, root5Node6Step2Chunk7_5_checked, root5Node6Step2Chunk8_0_checked, root5Node6Step2Chunk8_1_checked, root5Node6Step2Chunk8_2_checked, root5Node6Step2Chunk8_3_checked, root5Node6Step2Chunk8_4_checked, root5Node6Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
