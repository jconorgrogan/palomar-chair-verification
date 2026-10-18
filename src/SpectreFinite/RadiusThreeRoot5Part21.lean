module

public import SpectreFinite.RadiusThreeRoot5Part20
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable4
public import SpectreFinite.RadiusThreeTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node38Domains0 : Domains 37 State := restrict root5Node12Domains4 0 (8,0)
def root5Node38Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(4,4),(7,2),(8,4)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
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
theorem root5Node38Domains0_fast_eq : root5Node38Domains0 = expandDomains root5Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node38Domains0 v = expandDomains root5Node38Domains0Fast v from by decide) v
def root5Node38Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(8,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(0,0)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
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
def root5Node38Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(0,0)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
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
theorem root5Node38Domains1_fast_eq : root5Node38Domains1 = expandDomains root5Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node38Domains1 v = expandDomains root5Node38Domains1Fast v from by decide) v
theorem root5Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1_checked :
    checkReplacement table6 root5Node38Domains0 root5Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node38Step1Chunk0_0_checked, root5Node38Step1Chunk0_1_checked, root5Node38Step1Chunk0_2_checked, root5Node38Step1Chunk0_3_checked, root5Node38Step1Chunk0_4_checked, root5Node38Step1Chunk0_5_checked, root5Node38Step1Chunk1_0_checked, root5Node38Step1Chunk1_1_checked, root5Node38Step1Chunk1_2_checked, root5Node38Step1Chunk1_3_checked, root5Node38Step1Chunk1_4_checked, root5Node38Step1Chunk1_5_checked, root5Node38Step1Chunk2_0_checked, root5Node38Step1Chunk2_1_checked, root5Node38Step1Chunk2_2_checked, root5Node38Step1Chunk2_3_checked, root5Node38Step1Chunk2_4_checked, root5Node38Step1Chunk2_5_checked, root5Node38Step1Chunk3_0_checked, root5Node38Step1Chunk3_1_checked, root5Node38Step1Chunk3_2_checked, root5Node38Step1Chunk3_3_checked, root5Node38Step1Chunk3_4_checked, root5Node38Step1Chunk3_5_checked, root5Node38Step1Chunk4_0_checked, root5Node38Step1Chunk4_1_checked, root5Node38Step1Chunk4_2_checked, root5Node38Step1Chunk4_3_checked, root5Node38Step1Chunk4_4_checked, root5Node38Step1Chunk4_5_checked, root5Node38Step1Chunk5_0_checked, root5Node38Step1Chunk5_1_checked, root5Node38Step1Chunk5_2_checked, root5Node38Step1Chunk5_3_checked, root5Node38Step1Chunk5_4_checked, root5Node38Step1Chunk5_5_checked, root5Node38Step1Chunk6_0_checked, root5Node38Step1Chunk6_1_checked, root5Node38Step1Chunk6_2_checked, root5Node38Step1Chunk6_3_checked, root5Node38Step1Chunk6_4_checked, root5Node38Step1Chunk6_5_checked, root5Node38Step1Chunk7_0_checked, root5Node38Step1Chunk7_1_checked, root5Node38Step1Chunk7_2_checked, root5Node38Step1Chunk7_3_checked, root5Node38Step1Chunk7_4_checked, root5Node38Step1Chunk7_5_checked, root5Node38Step1Chunk8_0_checked, root5Node38Step1Chunk8_1_checked, root5Node38Step1Chunk8_2_checked, root5Node38Step1Chunk8_3_checked, root5Node38Step1Chunk8_4_checked, root5Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node38Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(8,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(0,0)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(8,3)]
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
  | 32 => [(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node38Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(0,0)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5)]
  | 14 => some [(6,1)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(8,3)]
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
  | 32 => some [(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node38Domains2_fast_eq : root5Node38Domains2 = expandDomains root5Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node38Domains2 v = expandDomains root5Node38Domains2Fast v from by decide) v
theorem root5Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2_checked :
    checkReplacement table26 root5Node38Domains1 root5Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node38Step2Chunk0_0_checked, root5Node38Step2Chunk0_1_checked, root5Node38Step2Chunk0_2_checked, root5Node38Step2Chunk0_3_checked, root5Node38Step2Chunk0_4_checked, root5Node38Step2Chunk0_5_checked, root5Node38Step2Chunk1_0_checked, root5Node38Step2Chunk1_1_checked, root5Node38Step2Chunk1_2_checked, root5Node38Step2Chunk1_3_checked, root5Node38Step2Chunk1_4_checked, root5Node38Step2Chunk1_5_checked, root5Node38Step2Chunk2_0_checked, root5Node38Step2Chunk2_1_checked, root5Node38Step2Chunk2_2_checked, root5Node38Step2Chunk2_3_checked, root5Node38Step2Chunk2_4_checked, root5Node38Step2Chunk2_5_checked, root5Node38Step2Chunk3_0_checked, root5Node38Step2Chunk3_1_checked, root5Node38Step2Chunk3_2_checked, root5Node38Step2Chunk3_3_checked, root5Node38Step2Chunk3_4_checked, root5Node38Step2Chunk3_5_checked, root5Node38Step2Chunk4_0_checked, root5Node38Step2Chunk4_1_checked, root5Node38Step2Chunk4_2_checked, root5Node38Step2Chunk4_3_checked, root5Node38Step2Chunk4_4_checked, root5Node38Step2Chunk4_5_checked, root5Node38Step2Chunk5_0_checked, root5Node38Step2Chunk5_1_checked, root5Node38Step2Chunk5_2_checked, root5Node38Step2Chunk5_3_checked, root5Node38Step2Chunk5_4_checked, root5Node38Step2Chunk5_5_checked, root5Node38Step2Chunk6_0_checked, root5Node38Step2Chunk6_1_checked, root5Node38Step2Chunk6_2_checked, root5Node38Step2Chunk6_3_checked, root5Node38Step2Chunk6_4_checked, root5Node38Step2Chunk6_5_checked, root5Node38Step2Chunk7_0_checked, root5Node38Step2Chunk7_1_checked, root5Node38Step2Chunk7_2_checked, root5Node38Step2Chunk7_3_checked, root5Node38Step2Chunk7_4_checked, root5Node38Step2Chunk7_5_checked, root5Node38Step2Chunk8_0_checked, root5Node38Step2Chunk8_1_checked, root5Node38Step2Chunk8_2_checked, root5Node38Step2Chunk8_3_checked, root5Node38Step2Chunk8_4_checked, root5Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node38Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(8,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(0,0)]
  | 9 => [(7,1)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5)]
  | 14 => [(6,1)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(8,3)]
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
  | 32 => [(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node38Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(8,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,1)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5)]
  | 14 => some [(6,1)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(8,3)]
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
  | 32 => some [(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node38Domains3_fast_eq : root5Node38Domains3 = expandDomains root5Node38Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node38Domains3 v = expandDomains root5Node38Domains3Fast v from by decide) v
theorem root5Node38Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node38Domains2 root5Node38Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains2 root5Node38Domains3
    root5Node38Domains2Fast root5Node38Domains3Fast
    root5Node38Domains2_fast_eq root5Node38Domains3_fast_eq (by decide)
theorem root5Node38Step3_checked :
    checkReplacement table4 root5Node38Domains2 root5Node38Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node38Step3Chunk0_0_checked, root5Node38Step3Chunk0_1_checked, root5Node38Step3Chunk0_2_checked, root5Node38Step3Chunk0_3_checked, root5Node38Step3Chunk0_4_checked, root5Node38Step3Chunk0_5_checked, root5Node38Step3Chunk1_0_checked, root5Node38Step3Chunk1_1_checked, root5Node38Step3Chunk1_2_checked, root5Node38Step3Chunk1_3_checked, root5Node38Step3Chunk1_4_checked, root5Node38Step3Chunk1_5_checked, root5Node38Step3Chunk2_0_checked, root5Node38Step3Chunk2_1_checked, root5Node38Step3Chunk2_2_checked, root5Node38Step3Chunk2_3_checked, root5Node38Step3Chunk2_4_checked, root5Node38Step3Chunk2_5_checked, root5Node38Step3Chunk3_0_checked, root5Node38Step3Chunk3_1_checked, root5Node38Step3Chunk3_2_checked, root5Node38Step3Chunk3_3_checked, root5Node38Step3Chunk3_4_checked, root5Node38Step3Chunk3_5_checked, root5Node38Step3Chunk4_0_checked, root5Node38Step3Chunk4_1_checked, root5Node38Step3Chunk4_2_checked, root5Node38Step3Chunk4_3_checked, root5Node38Step3Chunk4_4_checked, root5Node38Step3Chunk4_5_checked, root5Node38Step3Chunk5_0_checked, root5Node38Step3Chunk5_1_checked, root5Node38Step3Chunk5_2_checked, root5Node38Step3Chunk5_3_checked, root5Node38Step3Chunk5_4_checked, root5Node38Step3Chunk5_5_checked, root5Node38Step3Chunk6_0_checked, root5Node38Step3Chunk6_1_checked, root5Node38Step3Chunk6_2_checked, root5Node38Step3Chunk6_3_checked, root5Node38Step3Chunk6_4_checked, root5Node38Step3Chunk6_5_checked, root5Node38Step3Chunk7_0_checked, root5Node38Step3Chunk7_1_checked, root5Node38Step3Chunk7_2_checked, root5Node38Step3Chunk7_3_checked, root5Node38Step3Chunk7_4_checked, root5Node38Step3Chunk7_5_checked, root5Node38Step3Chunk8_0_checked, root5Node38Step3Chunk8_1_checked, root5Node38Step3Chunk8_2_checked, root5Node38Step3Chunk8_3_checked, root5Node38Step3Chunk8_4_checked, root5Node38Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
