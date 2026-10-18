module

public import SpectreFinite.RadiusThreeRoot5Part9
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable19
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node16Domains0 : Domains 37 State := restrict root5Node15Domains1 2 (3,5)
def root5Node16Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
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
theorem root5Node16Domains0_fast_eq : root5Node16Domains0 = expandDomains root5Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node16Domains0 v = expandDomains root5Node16Domains0Fast v from by decide) v
def root5Node16Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(2,4)]
  | 8 => [(1,3),(3,3)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
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
def root5Node16Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(2,4)]
  | 8 => some [(1,3),(3,3)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
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
theorem root5Node16Domains1_fast_eq : root5Node16Domains1 = expandDomains root5Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node16Domains1 v = expandDomains root5Node16Domains1Fast v from by decide) v
theorem root5Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1_checked :
    checkReplacement table11 root5Node16Domains0 root5Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node16Step1Chunk0_0_checked, root5Node16Step1Chunk0_1_checked, root5Node16Step1Chunk0_2_checked, root5Node16Step1Chunk0_3_checked, root5Node16Step1Chunk0_4_checked, root5Node16Step1Chunk0_5_checked, root5Node16Step1Chunk1_0_checked, root5Node16Step1Chunk1_1_checked, root5Node16Step1Chunk1_2_checked, root5Node16Step1Chunk1_3_checked, root5Node16Step1Chunk1_4_checked, root5Node16Step1Chunk1_5_checked, root5Node16Step1Chunk2_0_checked, root5Node16Step1Chunk2_1_checked, root5Node16Step1Chunk2_2_checked, root5Node16Step1Chunk2_3_checked, root5Node16Step1Chunk2_4_checked, root5Node16Step1Chunk2_5_checked, root5Node16Step1Chunk3_0_checked, root5Node16Step1Chunk3_1_checked, root5Node16Step1Chunk3_2_checked, root5Node16Step1Chunk3_3_checked, root5Node16Step1Chunk3_4_checked, root5Node16Step1Chunk3_5_checked, root5Node16Step1Chunk4_0_checked, root5Node16Step1Chunk4_1_checked, root5Node16Step1Chunk4_2_checked, root5Node16Step1Chunk4_3_checked, root5Node16Step1Chunk4_4_checked, root5Node16Step1Chunk4_5_checked, root5Node16Step1Chunk5_0_checked, root5Node16Step1Chunk5_1_checked, root5Node16Step1Chunk5_2_checked, root5Node16Step1Chunk5_3_checked, root5Node16Step1Chunk5_4_checked, root5Node16Step1Chunk5_5_checked, root5Node16Step1Chunk6_0_checked, root5Node16Step1Chunk6_1_checked, root5Node16Step1Chunk6_2_checked, root5Node16Step1Chunk6_3_checked, root5Node16Step1Chunk6_4_checked, root5Node16Step1Chunk6_5_checked, root5Node16Step1Chunk7_0_checked, root5Node16Step1Chunk7_1_checked, root5Node16Step1Chunk7_2_checked, root5Node16Step1Chunk7_3_checked, root5Node16Step1Chunk7_4_checked, root5Node16Step1Chunk7_5_checked, root5Node16Step1Chunk8_0_checked, root5Node16Step1Chunk8_1_checked, root5Node16Step1Chunk8_2_checked, root5Node16Step1Chunk8_3_checked, root5Node16Step1Chunk8_4_checked, root5Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node16Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(2,4)]
  | 8 => [(1,3)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node16Domains2Fast (v : Fin 37) : Option (List State) :=
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
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node16Domains2_fast_eq : root5Node16Domains2 = expandDomains root5Node16Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node16Domains2 v = expandDomains root5Node16Domains2Fast v from by decide) v
theorem root5Node16Step2Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root5Node16Domains1 root5Node16Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains1 root5Node16Domains2
    root5Node16Domains1Fast root5Node16Domains2Fast
    root5Node16Domains1_fast_eq root5Node16Domains2_fast_eq (by decide)
theorem root5Node16Step2_checked :
    checkReplacement table19 root5Node16Domains1 root5Node16Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node16Step2Chunk0_0_checked, root5Node16Step2Chunk0_1_checked, root5Node16Step2Chunk0_2_checked, root5Node16Step2Chunk0_3_checked, root5Node16Step2Chunk0_4_checked, root5Node16Step2Chunk0_5_checked, root5Node16Step2Chunk1_0_checked, root5Node16Step2Chunk1_1_checked, root5Node16Step2Chunk1_2_checked, root5Node16Step2Chunk1_3_checked, root5Node16Step2Chunk1_4_checked, root5Node16Step2Chunk1_5_checked, root5Node16Step2Chunk2_0_checked, root5Node16Step2Chunk2_1_checked, root5Node16Step2Chunk2_2_checked, root5Node16Step2Chunk2_3_checked, root5Node16Step2Chunk2_4_checked, root5Node16Step2Chunk2_5_checked, root5Node16Step2Chunk3_0_checked, root5Node16Step2Chunk3_1_checked, root5Node16Step2Chunk3_2_checked, root5Node16Step2Chunk3_3_checked, root5Node16Step2Chunk3_4_checked, root5Node16Step2Chunk3_5_checked, root5Node16Step2Chunk4_0_checked, root5Node16Step2Chunk4_1_checked, root5Node16Step2Chunk4_2_checked, root5Node16Step2Chunk4_3_checked, root5Node16Step2Chunk4_4_checked, root5Node16Step2Chunk4_5_checked, root5Node16Step2Chunk5_0_checked, root5Node16Step2Chunk5_1_checked, root5Node16Step2Chunk5_2_checked, root5Node16Step2Chunk5_3_checked, root5Node16Step2Chunk5_4_checked, root5Node16Step2Chunk5_5_checked, root5Node16Step2Chunk6_0_checked, root5Node16Step2Chunk6_1_checked, root5Node16Step2Chunk6_2_checked, root5Node16Step2Chunk6_3_checked, root5Node16Step2Chunk6_4_checked, root5Node16Step2Chunk6_5_checked, root5Node16Step2Chunk7_0_checked, root5Node16Step2Chunk7_1_checked, root5Node16Step2Chunk7_2_checked, root5Node16Step2Chunk7_3_checked, root5Node16Step2Chunk7_4_checked, root5Node16Step2Chunk7_5_checked, root5Node16Step2Chunk8_0_checked, root5Node16Step2Chunk8_1_checked, root5Node16Step2Chunk8_2_checked, root5Node16Step2Chunk8_3_checked, root5Node16Step2Chunk8_4_checked, root5Node16Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node16Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(2,4)]
  | 8 => [(1,3)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node16Domains3Fast (v : Fin 37) : Option (List State) :=
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
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node16Domains3_fast_eq : root5Node16Domains3 = expandDomains root5Node16Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node16Domains3 v = expandDomains root5Node16Domains3Fast v from by decide) v
theorem root5Node16Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node16Domains2 root5Node16Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains2 root5Node16Domains3
    root5Node16Domains2Fast root5Node16Domains3Fast
    root5Node16Domains2_fast_eq root5Node16Domains3_fast_eq (by decide)
theorem root5Node16Step3_checked :
    checkReplacement table4 root5Node16Domains2 root5Node16Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node16Step3Chunk0_0_checked, root5Node16Step3Chunk0_1_checked, root5Node16Step3Chunk0_2_checked, root5Node16Step3Chunk0_3_checked, root5Node16Step3Chunk0_4_checked, root5Node16Step3Chunk0_5_checked, root5Node16Step3Chunk1_0_checked, root5Node16Step3Chunk1_1_checked, root5Node16Step3Chunk1_2_checked, root5Node16Step3Chunk1_3_checked, root5Node16Step3Chunk1_4_checked, root5Node16Step3Chunk1_5_checked, root5Node16Step3Chunk2_0_checked, root5Node16Step3Chunk2_1_checked, root5Node16Step3Chunk2_2_checked, root5Node16Step3Chunk2_3_checked, root5Node16Step3Chunk2_4_checked, root5Node16Step3Chunk2_5_checked, root5Node16Step3Chunk3_0_checked, root5Node16Step3Chunk3_1_checked, root5Node16Step3Chunk3_2_checked, root5Node16Step3Chunk3_3_checked, root5Node16Step3Chunk3_4_checked, root5Node16Step3Chunk3_5_checked, root5Node16Step3Chunk4_0_checked, root5Node16Step3Chunk4_1_checked, root5Node16Step3Chunk4_2_checked, root5Node16Step3Chunk4_3_checked, root5Node16Step3Chunk4_4_checked, root5Node16Step3Chunk4_5_checked, root5Node16Step3Chunk5_0_checked, root5Node16Step3Chunk5_1_checked, root5Node16Step3Chunk5_2_checked, root5Node16Step3Chunk5_3_checked, root5Node16Step3Chunk5_4_checked, root5Node16Step3Chunk5_5_checked, root5Node16Step3Chunk6_0_checked, root5Node16Step3Chunk6_1_checked, root5Node16Step3Chunk6_2_checked, root5Node16Step3Chunk6_3_checked, root5Node16Step3Chunk6_4_checked, root5Node16Step3Chunk6_5_checked, root5Node16Step3Chunk7_0_checked, root5Node16Step3Chunk7_1_checked, root5Node16Step3Chunk7_2_checked, root5Node16Step3Chunk7_3_checked, root5Node16Step3Chunk7_4_checked, root5Node16Step3Chunk7_5_checked, root5Node16Step3Chunk8_0_checked, root5Node16Step3Chunk8_1_checked, root5Node16Step3Chunk8_2_checked, root5Node16Step3Chunk8_3_checked, root5Node16Step3Chunk8_4_checked, root5Node16Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
