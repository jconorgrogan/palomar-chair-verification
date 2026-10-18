module

public import SpectreFinite.RadiusThreeRoot5Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable12
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node22Domains0 : Domains 37 State := restrict root5Node20Domains1 34 (8,5)
def root5Node22Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,4)]
  | 8 => some [(1,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(0,3)]
  | 29 => some [(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node22Domains0_fast_eq : root5Node22Domains0 = expandDomains root5Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node22Domains0 v = expandDomains root5Node22Domains0Fast v from by decide) v
theorem root5Node22Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node22Domains0 (.output 9) = true := by decide
def root5Node23Domains0 : Domains 37 State := restrict root5Node15Domains1 2 (7,5)
def root5Node23Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,2),(2,4)]
  | 8 => some [(1,3),(3,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(0,1),(6,5)]
  | 14 => some [(0,4),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node23Domains0_fast_eq : root5Node23Domains0 = expandDomains root5Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node23Domains0 v = expandDomains root5Node23Domains0Fast v from by decide) v
def root5Node23Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(4,4),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(2,2)]
  | 8 => [(3,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(4,3),(7,1)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node23Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(2,2)]
  | 8 => some [(3,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(4,3),(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node23Domains1_fast_eq : root5Node23Domains1 = expandDomains root5Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node23Domains1 v = expandDomains root5Node23Domains1Fast v from by decide) v
theorem root5Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node23Domains0 root5Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains0 root5Node23Domains1
    root5Node23Domains0Fast root5Node23Domains1Fast
    root5Node23Domains0_fast_eq root5Node23Domains1_fast_eq (by decide)
theorem root5Node23Step1_checked :
    checkReplacement table12 root5Node23Domains0 root5Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node23Step1Chunk0_0_checked, root5Node23Step1Chunk0_1_checked, root5Node23Step1Chunk0_2_checked, root5Node23Step1Chunk0_3_checked, root5Node23Step1Chunk0_4_checked, root5Node23Step1Chunk0_5_checked, root5Node23Step1Chunk1_0_checked, root5Node23Step1Chunk1_1_checked, root5Node23Step1Chunk1_2_checked, root5Node23Step1Chunk1_3_checked, root5Node23Step1Chunk1_4_checked, root5Node23Step1Chunk1_5_checked, root5Node23Step1Chunk2_0_checked, root5Node23Step1Chunk2_1_checked, root5Node23Step1Chunk2_2_checked, root5Node23Step1Chunk2_3_checked, root5Node23Step1Chunk2_4_checked, root5Node23Step1Chunk2_5_checked, root5Node23Step1Chunk3_0_checked, root5Node23Step1Chunk3_1_checked, root5Node23Step1Chunk3_2_checked, root5Node23Step1Chunk3_3_checked, root5Node23Step1Chunk3_4_checked, root5Node23Step1Chunk3_5_checked, root5Node23Step1Chunk4_0_checked, root5Node23Step1Chunk4_1_checked, root5Node23Step1Chunk4_2_checked, root5Node23Step1Chunk4_3_checked, root5Node23Step1Chunk4_4_checked, root5Node23Step1Chunk4_5_checked, root5Node23Step1Chunk5_0_checked, root5Node23Step1Chunk5_1_checked, root5Node23Step1Chunk5_2_checked, root5Node23Step1Chunk5_3_checked, root5Node23Step1Chunk5_4_checked, root5Node23Step1Chunk5_5_checked, root5Node23Step1Chunk6_0_checked, root5Node23Step1Chunk6_1_checked, root5Node23Step1Chunk6_2_checked, root5Node23Step1Chunk6_3_checked, root5Node23Step1Chunk6_4_checked, root5Node23Step1Chunk6_5_checked, root5Node23Step1Chunk7_0_checked, root5Node23Step1Chunk7_1_checked, root5Node23Step1Chunk7_2_checked, root5Node23Step1Chunk7_3_checked, root5Node23Step1Chunk7_4_checked, root5Node23Step1Chunk7_5_checked, root5Node23Step1Chunk8_0_checked, root5Node23Step1Chunk8_1_checked, root5Node23Step1Chunk8_2_checked, root5Node23Step1Chunk8_3_checked, root5Node23Step1Chunk8_4_checked, root5Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node23Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(4,4),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(2,2)]
  | 8 => [(3,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,1)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node23Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(2,2)]
  | 8 => some [(3,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node23Domains2_fast_eq : root5Node23Domains2 = expandDomains root5Node23Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node23Domains2 v = expandDomains root5Node23Domains2Fast v from by decide) v
theorem root5Node23Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root5Node23Domains1 root5Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node23Domains1 root5Node23Domains2
    root5Node23Domains1Fast root5Node23Domains2Fast
    root5Node23Domains1_fast_eq root5Node23Domains2_fast_eq (by decide)
theorem root5Node23Step2_checked :
    checkReplacement table26 root5Node23Domains1 root5Node23Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node23Step2Chunk0_0_checked, root5Node23Step2Chunk0_1_checked, root5Node23Step2Chunk0_2_checked, root5Node23Step2Chunk0_3_checked, root5Node23Step2Chunk0_4_checked, root5Node23Step2Chunk0_5_checked, root5Node23Step2Chunk1_0_checked, root5Node23Step2Chunk1_1_checked, root5Node23Step2Chunk1_2_checked, root5Node23Step2Chunk1_3_checked, root5Node23Step2Chunk1_4_checked, root5Node23Step2Chunk1_5_checked, root5Node23Step2Chunk2_0_checked, root5Node23Step2Chunk2_1_checked, root5Node23Step2Chunk2_2_checked, root5Node23Step2Chunk2_3_checked, root5Node23Step2Chunk2_4_checked, root5Node23Step2Chunk2_5_checked, root5Node23Step2Chunk3_0_checked, root5Node23Step2Chunk3_1_checked, root5Node23Step2Chunk3_2_checked, root5Node23Step2Chunk3_3_checked, root5Node23Step2Chunk3_4_checked, root5Node23Step2Chunk3_5_checked, root5Node23Step2Chunk4_0_checked, root5Node23Step2Chunk4_1_checked, root5Node23Step2Chunk4_2_checked, root5Node23Step2Chunk4_3_checked, root5Node23Step2Chunk4_4_checked, root5Node23Step2Chunk4_5_checked, root5Node23Step2Chunk5_0_checked, root5Node23Step2Chunk5_1_checked, root5Node23Step2Chunk5_2_checked, root5Node23Step2Chunk5_3_checked, root5Node23Step2Chunk5_4_checked, root5Node23Step2Chunk5_5_checked, root5Node23Step2Chunk6_0_checked, root5Node23Step2Chunk6_1_checked, root5Node23Step2Chunk6_2_checked, root5Node23Step2Chunk6_3_checked, root5Node23Step2Chunk6_4_checked, root5Node23Step2Chunk6_5_checked, root5Node23Step2Chunk7_0_checked, root5Node23Step2Chunk7_1_checked, root5Node23Step2Chunk7_2_checked, root5Node23Step2Chunk7_3_checked, root5Node23Step2Chunk7_4_checked, root5Node23Step2Chunk7_5_checked, root5Node23Step2Chunk8_0_checked, root5Node23Step2Chunk8_1_checked, root5Node23Step2Chunk8_2_checked, root5Node23Step2Chunk8_3_checked, root5Node23Step2Chunk8_4_checked, root5Node23Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
