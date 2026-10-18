module

public import SpectreFinite.RadiusThreeRoot7Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable24

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node7Domains0 : Domains 37 State := restrict root7Node5Domains2 35 (8,5)
def root7Node7Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(1,0)]
  | 2 => some [(2,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(3,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(7,0)]
theorem root7Node7Domains0_fast_eq : root7Node7Domains0 = expandDomains root7Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node7Domains0 v = expandDomains root7Node7Domains0Fast v from by decide) v
theorem root7Node7Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node7Domains0 (.output 2) = true := by decide
def root7Node8Domains0 : Domains 37 State := restrict root7Node2Domains5 1 (3,0)
def root7Node8Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(3,0)]
  | 2 => some [(2,1),(2,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(3,2),(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(5,4),(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(7,0),(8,0)]
theorem root7Node8Domains0_fast_eq : root7Node8Domains0 = expandDomains root7Node8Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node8Domains0 v = expandDomains root7Node8Domains0Fast v from by decide) v
def root7Node8Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,5)]
  | 1 => [(3,0)]
  | 2 => [(2,5)]
  | 3 => [(6,0)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(5,4),(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0),(7,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(7,0),(8,0)]
def root7Node8Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(3,0)]
  | 2 => some [(2,5)]
  | 3 => some [(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(5,4),(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(7,0),(8,0)]
theorem root7Node8Domains1_fast_eq : root7Node8Domains1 = expandDomains root7Node8Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node8Domains1 v = expandDomains root7Node8Domains1Fast v from by decide) v
theorem root7Node8Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root7Node8Domains0 root7Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node8Domains0 root7Node8Domains1
    root7Node8Domains0Fast root7Node8Domains1Fast
    root7Node8Domains0_fast_eq root7Node8Domains1_fast_eq (by decide)
theorem root7Node8Step1_checked :
    checkReplacement table1 root7Node8Domains0 root7Node8Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node8Step1Chunk0_0_checked, root7Node8Step1Chunk0_1_checked, root7Node8Step1Chunk0_2_checked, root7Node8Step1Chunk0_3_checked, root7Node8Step1Chunk0_4_checked, root7Node8Step1Chunk0_5_checked, root7Node8Step1Chunk1_0_checked, root7Node8Step1Chunk1_1_checked, root7Node8Step1Chunk1_2_checked, root7Node8Step1Chunk1_3_checked, root7Node8Step1Chunk1_4_checked, root7Node8Step1Chunk1_5_checked, root7Node8Step1Chunk2_0_checked, root7Node8Step1Chunk2_1_checked, root7Node8Step1Chunk2_2_checked, root7Node8Step1Chunk2_3_checked, root7Node8Step1Chunk2_4_checked, root7Node8Step1Chunk2_5_checked, root7Node8Step1Chunk3_0_checked, root7Node8Step1Chunk3_1_checked, root7Node8Step1Chunk3_2_checked, root7Node8Step1Chunk3_3_checked, root7Node8Step1Chunk3_4_checked, root7Node8Step1Chunk3_5_checked, root7Node8Step1Chunk4_0_checked, root7Node8Step1Chunk4_1_checked, root7Node8Step1Chunk4_2_checked, root7Node8Step1Chunk4_3_checked, root7Node8Step1Chunk4_4_checked, root7Node8Step1Chunk4_5_checked, root7Node8Step1Chunk5_0_checked, root7Node8Step1Chunk5_1_checked, root7Node8Step1Chunk5_2_checked, root7Node8Step1Chunk5_3_checked, root7Node8Step1Chunk5_4_checked, root7Node8Step1Chunk5_5_checked, root7Node8Step1Chunk6_0_checked, root7Node8Step1Chunk6_1_checked, root7Node8Step1Chunk6_2_checked, root7Node8Step1Chunk6_3_checked, root7Node8Step1Chunk6_4_checked, root7Node8Step1Chunk6_5_checked, root7Node8Step1Chunk7_0_checked, root7Node8Step1Chunk7_1_checked, root7Node8Step1Chunk7_2_checked, root7Node8Step1Chunk7_3_checked, root7Node8Step1Chunk7_4_checked, root7Node8Step1Chunk7_5_checked, root7Node8Step1Chunk8_0_checked, root7Node8Step1Chunk8_1_checked, root7Node8Step1Chunk8_2_checked, root7Node8Step1Chunk8_3_checked, root7Node8Step1Chunk8_4_checked, root7Node8Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node9Domains0 : Domains 37 State := restrict root7Node8Domains1 22 (5,4)
def root7Node9Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(3,0)]
  | 2 => some [(2,5)]
  | 3 => some [(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(5,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(7,0),(8,0)]
theorem root7Node9Domains0_fast_eq : root7Node9Domains0 = expandDomains root7Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node9Domains0 v = expandDomains root7Node9Domains0Fast v from by decide) v
def root7Node9Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(5,5)]
  | 1 => [(3,0)]
  | 2 => [(2,5)]
  | 3 => [(6,0)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(5,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(6,3)]
  | 27 => [(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0)]
  | 34 => [(7,3)]
  | 35 => [(5,2)]
  | _ => [(7,0),(8,0)]
def root7Node9Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(5,5)]
  | 1 => some [(3,0)]
  | 2 => some [(2,5)]
  | 3 => some [(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(5,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(6,3)]
  | 27 => some [(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2)]
  | _ => some [(7,0),(8,0)]
theorem root7Node9Domains1_fast_eq : root7Node9Domains1 = expandDomains root7Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node9Domains1 v = expandDomains root7Node9Domains1Fast v from by decide) v
theorem root7Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root7Node9Domains0 root7Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node9Domains0 root7Node9Domains1
    root7Node9Domains0Fast root7Node9Domains1Fast
    root7Node9Domains0_fast_eq root7Node9Domains1_fast_eq (by decide)
theorem root7Node9Step1_checked :
    checkReplacement table24 root7Node9Domains0 root7Node9Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node9Step1Chunk0_0_checked, root7Node9Step1Chunk0_1_checked, root7Node9Step1Chunk0_2_checked, root7Node9Step1Chunk0_3_checked, root7Node9Step1Chunk0_4_checked, root7Node9Step1Chunk0_5_checked, root7Node9Step1Chunk1_0_checked, root7Node9Step1Chunk1_1_checked, root7Node9Step1Chunk1_2_checked, root7Node9Step1Chunk1_3_checked, root7Node9Step1Chunk1_4_checked, root7Node9Step1Chunk1_5_checked, root7Node9Step1Chunk2_0_checked, root7Node9Step1Chunk2_1_checked, root7Node9Step1Chunk2_2_checked, root7Node9Step1Chunk2_3_checked, root7Node9Step1Chunk2_4_checked, root7Node9Step1Chunk2_5_checked, root7Node9Step1Chunk3_0_checked, root7Node9Step1Chunk3_1_checked, root7Node9Step1Chunk3_2_checked, root7Node9Step1Chunk3_3_checked, root7Node9Step1Chunk3_4_checked, root7Node9Step1Chunk3_5_checked, root7Node9Step1Chunk4_0_checked, root7Node9Step1Chunk4_1_checked, root7Node9Step1Chunk4_2_checked, root7Node9Step1Chunk4_3_checked, root7Node9Step1Chunk4_4_checked, root7Node9Step1Chunk4_5_checked, root7Node9Step1Chunk5_0_checked, root7Node9Step1Chunk5_1_checked, root7Node9Step1Chunk5_2_checked, root7Node9Step1Chunk5_3_checked, root7Node9Step1Chunk5_4_checked, root7Node9Step1Chunk5_5_checked, root7Node9Step1Chunk6_0_checked, root7Node9Step1Chunk6_1_checked, root7Node9Step1Chunk6_2_checked, root7Node9Step1Chunk6_3_checked, root7Node9Step1Chunk6_4_checked, root7Node9Step1Chunk6_5_checked, root7Node9Step1Chunk7_0_checked, root7Node9Step1Chunk7_1_checked, root7Node9Step1Chunk7_2_checked, root7Node9Step1Chunk7_3_checked, root7Node9Step1Chunk7_4_checked, root7Node9Step1Chunk7_5_checked, root7Node9Step1Chunk8_0_checked, root7Node9Step1Chunk8_1_checked, root7Node9Step1Chunk8_2_checked, root7Node9Step1Chunk8_3_checked, root7Node9Step1Chunk8_4_checked, root7Node9Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
