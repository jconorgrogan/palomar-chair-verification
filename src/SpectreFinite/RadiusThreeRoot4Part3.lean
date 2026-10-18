module

public import SpectreFinite.RadiusThreeRoot4Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable16
public import SpectreFinite.RadiusThreeTable7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node3Domains0 : Domains 37 State := restrict root4Node2Domains3 2 (5,5)
def root4Node3Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(1,4),(3,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(4,4),(7,2)]
  | 8 => some [(1,4),(6,4),(7,4)]
  | 9 => some [(1,0),(3,0),(7,0)]
  | 10 => some [(2,1),(2,3),(2,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(7,5)]
  | 14 => some [(0,2),(0,3),(6,0)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0),(6,4)]
  | 17 => some [(1,2),(3,2),(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(5,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(1,5),(7,5)]
  | 23 => some [(0,3),(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(4,2),(7,0)]
  | 29 => some [(5,3),(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node3Domains0_fast_eq : root4Node3Domains0 = expandDomains root4Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node3Domains0 v = expandDomains root4Node3Domains0Fast v from by decide) v
def root4Node3Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(1,4),(6,4),(7,4)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,2),(0,3),(6,0)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(5,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(1,5),(7,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(4,2),(7,0)]
  | 29 => [(5,3),(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3),(6,3)]
  | 35 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root4Node3Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(1,4),(6,4),(7,4)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,2),(0,3),(6,0)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(5,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(1,5),(7,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(4,2),(7,0)]
  | 29 => some [(5,3),(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node3Domains1_fast_eq : root4Node3Domains1 = expandDomains root4Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node3Domains1 v = expandDomains root4Node3Domains1Fast v from by decide) v
theorem root4Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root4Node3Domains0 root4Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains0 root4Node3Domains1
    root4Node3Domains0Fast root4Node3Domains1Fast
    root4Node3Domains0_fast_eq root4Node3Domains1_fast_eq (by decide)
theorem root4Node3Step1_checked :
    checkReplacement table11 root4Node3Domains0 root4Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node3Step1Chunk0_0_checked, root4Node3Step1Chunk0_1_checked, root4Node3Step1Chunk0_2_checked, root4Node3Step1Chunk0_3_checked, root4Node3Step1Chunk0_4_checked, root4Node3Step1Chunk0_5_checked, root4Node3Step1Chunk1_0_checked, root4Node3Step1Chunk1_1_checked, root4Node3Step1Chunk1_2_checked, root4Node3Step1Chunk1_3_checked, root4Node3Step1Chunk1_4_checked, root4Node3Step1Chunk1_5_checked, root4Node3Step1Chunk2_0_checked, root4Node3Step1Chunk2_1_checked, root4Node3Step1Chunk2_2_checked, root4Node3Step1Chunk2_3_checked, root4Node3Step1Chunk2_4_checked, root4Node3Step1Chunk2_5_checked, root4Node3Step1Chunk3_0_checked, root4Node3Step1Chunk3_1_checked, root4Node3Step1Chunk3_2_checked, root4Node3Step1Chunk3_3_checked, root4Node3Step1Chunk3_4_checked, root4Node3Step1Chunk3_5_checked, root4Node3Step1Chunk4_0_checked, root4Node3Step1Chunk4_1_checked, root4Node3Step1Chunk4_2_checked, root4Node3Step1Chunk4_3_checked, root4Node3Step1Chunk4_4_checked, root4Node3Step1Chunk4_5_checked, root4Node3Step1Chunk5_0_checked, root4Node3Step1Chunk5_1_checked, root4Node3Step1Chunk5_2_checked, root4Node3Step1Chunk5_3_checked, root4Node3Step1Chunk5_4_checked, root4Node3Step1Chunk5_5_checked, root4Node3Step1Chunk6_0_checked, root4Node3Step1Chunk6_1_checked, root4Node3Step1Chunk6_2_checked, root4Node3Step1Chunk6_3_checked, root4Node3Step1Chunk6_4_checked, root4Node3Step1Chunk6_5_checked, root4Node3Step1Chunk7_0_checked, root4Node3Step1Chunk7_1_checked, root4Node3Step1Chunk7_2_checked, root4Node3Step1Chunk7_3_checked, root4Node3Step1Chunk7_4_checked, root4Node3Step1Chunk7_5_checked, root4Node3Step1Chunk8_0_checked, root4Node3Step1Chunk8_1_checked, root4Node3Step1Chunk8_2_checked, root4Node3Step1Chunk8_3_checked, root4Node3Step1Chunk8_4_checked, root4Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node3Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(1,5),(7,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(4,2),(7,0)]
  | 29 => [(5,3),(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3),(6,3)]
  | 35 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root4Node3Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(1,5),(7,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(4,2),(7,0)]
  | 29 => some [(5,3),(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node3Domains2_fast_eq : root4Node3Domains2 = expandDomains root4Node3Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node3Domains2 v = expandDomains root4Node3Domains2Fast v from by decide) v
theorem root4Node3Step2Chunk0_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk0_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk0_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk0_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk0_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk0_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk1_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk1_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk1_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk1_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk1_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk1_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk2_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk2_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk2_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk2_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk2_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk2_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk3_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk3_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk3_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk3_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk3_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk3_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk4_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk4_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk4_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk4_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk4_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk4_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk5_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk5_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk5_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk5_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk5_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk5_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk6_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk6_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk6_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk6_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk6_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk6_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk7_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk7_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk7_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk7_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk7_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk7_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk8_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_0⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk8_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_1⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk8_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_2⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk8_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_3⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk8_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_4⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2Chunk8_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_5⟩
      root4Node3Domains1 root4Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains1 root4Node3Domains2
    root4Node3Domains1Fast root4Node3Domains2Fast
    root4Node3Domains1_fast_eq root4Node3Domains2_fast_eq (by decide)
theorem root4Node3Step2_checked :
    checkReplacement table7 root4Node3Domains1 root4Node3Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node3Step2Chunk0_0_checked, root4Node3Step2Chunk0_1_checked, root4Node3Step2Chunk0_2_checked, root4Node3Step2Chunk0_3_checked, root4Node3Step2Chunk0_4_checked, root4Node3Step2Chunk0_5_checked, root4Node3Step2Chunk1_0_checked, root4Node3Step2Chunk1_1_checked, root4Node3Step2Chunk1_2_checked, root4Node3Step2Chunk1_3_checked, root4Node3Step2Chunk1_4_checked, root4Node3Step2Chunk1_5_checked, root4Node3Step2Chunk2_0_checked, root4Node3Step2Chunk2_1_checked, root4Node3Step2Chunk2_2_checked, root4Node3Step2Chunk2_3_checked, root4Node3Step2Chunk2_4_checked, root4Node3Step2Chunk2_5_checked, root4Node3Step2Chunk3_0_checked, root4Node3Step2Chunk3_1_checked, root4Node3Step2Chunk3_2_checked, root4Node3Step2Chunk3_3_checked, root4Node3Step2Chunk3_4_checked, root4Node3Step2Chunk3_5_checked, root4Node3Step2Chunk4_0_checked, root4Node3Step2Chunk4_1_checked, root4Node3Step2Chunk4_2_checked, root4Node3Step2Chunk4_3_checked, root4Node3Step2Chunk4_4_checked, root4Node3Step2Chunk4_5_checked, root4Node3Step2Chunk5_0_checked, root4Node3Step2Chunk5_1_checked, root4Node3Step2Chunk5_2_checked, root4Node3Step2Chunk5_3_checked, root4Node3Step2Chunk5_4_checked, root4Node3Step2Chunk5_5_checked, root4Node3Step2Chunk6_0_checked, root4Node3Step2Chunk6_1_checked, root4Node3Step2Chunk6_2_checked, root4Node3Step2Chunk6_3_checked, root4Node3Step2Chunk6_4_checked, root4Node3Step2Chunk6_5_checked, root4Node3Step2Chunk7_0_checked, root4Node3Step2Chunk7_1_checked, root4Node3Step2Chunk7_2_checked, root4Node3Step2Chunk7_3_checked, root4Node3Step2Chunk7_4_checked, root4Node3Step2Chunk7_5_checked, root4Node3Step2Chunk8_0_checked, root4Node3Step2Chunk8_1_checked, root4Node3Step2Chunk8_2_checked, root4Node3Step2Chunk8_3_checked, root4Node3Step2Chunk8_4_checked, root4Node3Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node3Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(1,4),(6,4)]
  | 9 => [(3,0)]
  | 10 => [(2,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3),(6,0)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(1,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(7,0)]
  | 29 => [(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3),(6,3)]
  | 35 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root4Node3Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(1,4),(6,4)]
  | 9 => some [(3,0)]
  | 10 => some [(2,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node3Domains3_fast_eq : root4Node3Domains3 = expandDomains root4Node3Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node3Domains3 v = expandDomains root4Node3Domains3Fast v from by decide) v
theorem root4Node3Step3Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root4Node3Domains2 root4Node3Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node3Domains2 root4Node3Domains3
    root4Node3Domains2Fast root4Node3Domains3Fast
    root4Node3Domains2_fast_eq root4Node3Domains3_fast_eq (by decide)
theorem root4Node3Step3_checked :
    checkReplacement table16 root4Node3Domains2 root4Node3Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node3Step3Chunk0_0_checked, root4Node3Step3Chunk0_1_checked, root4Node3Step3Chunk0_2_checked, root4Node3Step3Chunk0_3_checked, root4Node3Step3Chunk0_4_checked, root4Node3Step3Chunk0_5_checked, root4Node3Step3Chunk1_0_checked, root4Node3Step3Chunk1_1_checked, root4Node3Step3Chunk1_2_checked, root4Node3Step3Chunk1_3_checked, root4Node3Step3Chunk1_4_checked, root4Node3Step3Chunk1_5_checked, root4Node3Step3Chunk2_0_checked, root4Node3Step3Chunk2_1_checked, root4Node3Step3Chunk2_2_checked, root4Node3Step3Chunk2_3_checked, root4Node3Step3Chunk2_4_checked, root4Node3Step3Chunk2_5_checked, root4Node3Step3Chunk3_0_checked, root4Node3Step3Chunk3_1_checked, root4Node3Step3Chunk3_2_checked, root4Node3Step3Chunk3_3_checked, root4Node3Step3Chunk3_4_checked, root4Node3Step3Chunk3_5_checked, root4Node3Step3Chunk4_0_checked, root4Node3Step3Chunk4_1_checked, root4Node3Step3Chunk4_2_checked, root4Node3Step3Chunk4_3_checked, root4Node3Step3Chunk4_4_checked, root4Node3Step3Chunk4_5_checked, root4Node3Step3Chunk5_0_checked, root4Node3Step3Chunk5_1_checked, root4Node3Step3Chunk5_2_checked, root4Node3Step3Chunk5_3_checked, root4Node3Step3Chunk5_4_checked, root4Node3Step3Chunk5_5_checked, root4Node3Step3Chunk6_0_checked, root4Node3Step3Chunk6_1_checked, root4Node3Step3Chunk6_2_checked, root4Node3Step3Chunk6_3_checked, root4Node3Step3Chunk6_4_checked, root4Node3Step3Chunk6_5_checked, root4Node3Step3Chunk7_0_checked, root4Node3Step3Chunk7_1_checked, root4Node3Step3Chunk7_2_checked, root4Node3Step3Chunk7_3_checked, root4Node3Step3Chunk7_4_checked, root4Node3Step3Chunk7_5_checked, root4Node3Step3Chunk8_0_checked, root4Node3Step3Chunk8_1_checked, root4Node3Step3Chunk8_2_checked, root4Node3Step3Chunk8_3_checked, root4Node3Step3Chunk8_4_checked, root4Node3Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
