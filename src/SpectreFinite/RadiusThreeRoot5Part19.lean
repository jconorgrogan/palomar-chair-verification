module

public import SpectreFinite.RadiusThreeRoot5Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable10
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node35Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(4,4)]
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
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
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
def root5Node35Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(4,4)]
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
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
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
theorem root5Node35Domains2_fast_eq : root5Node35Domains2 = expandDomains root5Node35Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node35Domains2 v = expandDomains root5Node35Domains2Fast v from by decide) v
theorem root5Node35Step2Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root5Node35Domains1 root5Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains1 root5Node35Domains2
    root5Node35Domains1Fast root5Node35Domains2Fast
    root5Node35Domains1_fast_eq root5Node35Domains2_fast_eq (by decide)
theorem root5Node35Step2_checked :
    checkReplacement table10 root5Node35Domains1 root5Node35Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node35Step2Chunk0_0_checked, root5Node35Step2Chunk0_1_checked, root5Node35Step2Chunk0_2_checked, root5Node35Step2Chunk0_3_checked, root5Node35Step2Chunk0_4_checked, root5Node35Step2Chunk0_5_checked, root5Node35Step2Chunk1_0_checked, root5Node35Step2Chunk1_1_checked, root5Node35Step2Chunk1_2_checked, root5Node35Step2Chunk1_3_checked, root5Node35Step2Chunk1_4_checked, root5Node35Step2Chunk1_5_checked, root5Node35Step2Chunk2_0_checked, root5Node35Step2Chunk2_1_checked, root5Node35Step2Chunk2_2_checked, root5Node35Step2Chunk2_3_checked, root5Node35Step2Chunk2_4_checked, root5Node35Step2Chunk2_5_checked, root5Node35Step2Chunk3_0_checked, root5Node35Step2Chunk3_1_checked, root5Node35Step2Chunk3_2_checked, root5Node35Step2Chunk3_3_checked, root5Node35Step2Chunk3_4_checked, root5Node35Step2Chunk3_5_checked, root5Node35Step2Chunk4_0_checked, root5Node35Step2Chunk4_1_checked, root5Node35Step2Chunk4_2_checked, root5Node35Step2Chunk4_3_checked, root5Node35Step2Chunk4_4_checked, root5Node35Step2Chunk4_5_checked, root5Node35Step2Chunk5_0_checked, root5Node35Step2Chunk5_1_checked, root5Node35Step2Chunk5_2_checked, root5Node35Step2Chunk5_3_checked, root5Node35Step2Chunk5_4_checked, root5Node35Step2Chunk5_5_checked, root5Node35Step2Chunk6_0_checked, root5Node35Step2Chunk6_1_checked, root5Node35Step2Chunk6_2_checked, root5Node35Step2Chunk6_3_checked, root5Node35Step2Chunk6_4_checked, root5Node35Step2Chunk6_5_checked, root5Node35Step2Chunk7_0_checked, root5Node35Step2Chunk7_1_checked, root5Node35Step2Chunk7_2_checked, root5Node35Step2Chunk7_3_checked, root5Node35Step2Chunk7_4_checked, root5Node35Step2Chunk7_5_checked, root5Node35Step2Chunk8_0_checked, root5Node35Step2Chunk8_1_checked, root5Node35Step2Chunk8_2_checked, root5Node35Step2Chunk8_3_checked, root5Node35Step2Chunk8_4_checked, root5Node35Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node35Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(4,4)]
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
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node35Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(4,4)]
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
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node35Domains3_fast_eq : root5Node35Domains3 = expandDomains root5Node35Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node35Domains3 v = expandDomains root5Node35Domains3Fast v from by decide) v
theorem root5Node35Step3Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root5Node35Domains2 root5Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains2 root5Node35Domains3
    root5Node35Domains2Fast root5Node35Domains3Fast
    root5Node35Domains2_fast_eq root5Node35Domains3_fast_eq (by decide)
theorem root5Node35Step3_checked :
    checkReplacement table25 root5Node35Domains2 root5Node35Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node35Step3Chunk0_0_checked, root5Node35Step3Chunk0_1_checked, root5Node35Step3Chunk0_2_checked, root5Node35Step3Chunk0_3_checked, root5Node35Step3Chunk0_4_checked, root5Node35Step3Chunk0_5_checked, root5Node35Step3Chunk1_0_checked, root5Node35Step3Chunk1_1_checked, root5Node35Step3Chunk1_2_checked, root5Node35Step3Chunk1_3_checked, root5Node35Step3Chunk1_4_checked, root5Node35Step3Chunk1_5_checked, root5Node35Step3Chunk2_0_checked, root5Node35Step3Chunk2_1_checked, root5Node35Step3Chunk2_2_checked, root5Node35Step3Chunk2_3_checked, root5Node35Step3Chunk2_4_checked, root5Node35Step3Chunk2_5_checked, root5Node35Step3Chunk3_0_checked, root5Node35Step3Chunk3_1_checked, root5Node35Step3Chunk3_2_checked, root5Node35Step3Chunk3_3_checked, root5Node35Step3Chunk3_4_checked, root5Node35Step3Chunk3_5_checked, root5Node35Step3Chunk4_0_checked, root5Node35Step3Chunk4_1_checked, root5Node35Step3Chunk4_2_checked, root5Node35Step3Chunk4_3_checked, root5Node35Step3Chunk4_4_checked, root5Node35Step3Chunk4_5_checked, root5Node35Step3Chunk5_0_checked, root5Node35Step3Chunk5_1_checked, root5Node35Step3Chunk5_2_checked, root5Node35Step3Chunk5_3_checked, root5Node35Step3Chunk5_4_checked, root5Node35Step3Chunk5_5_checked, root5Node35Step3Chunk6_0_checked, root5Node35Step3Chunk6_1_checked, root5Node35Step3Chunk6_2_checked, root5Node35Step3Chunk6_3_checked, root5Node35Step3Chunk6_4_checked, root5Node35Step3Chunk6_5_checked, root5Node35Step3Chunk7_0_checked, root5Node35Step3Chunk7_1_checked, root5Node35Step3Chunk7_2_checked, root5Node35Step3Chunk7_3_checked, root5Node35Step3Chunk7_4_checked, root5Node35Step3Chunk7_5_checked, root5Node35Step3Chunk8_0_checked, root5Node35Step3Chunk8_1_checked, root5Node35Step3Chunk8_2_checked, root5Node35Step3Chunk8_3_checked, root5Node35Step3Chunk8_4_checked, root5Node35Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node35Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(4,4)]
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
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(8,3)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node35Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(4,4)]
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
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(8,3)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node35Domains4_fast_eq : root5Node35Domains4 = expandDomains root5Node35Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node35Domains4 v = expandDomains root5Node35Domains4Fast v from by decide) v
theorem root5Node35Step4Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root5Node35Domains3 root5Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains3 root5Node35Domains4
    root5Node35Domains3Fast root5Node35Domains4Fast
    root5Node35Domains3_fast_eq root5Node35Domains4_fast_eq (by decide)
theorem root5Node35Step4_checked :
    checkReplacement table8 root5Node35Domains3 root5Node35Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node35Step4Chunk0_0_checked, root5Node35Step4Chunk0_1_checked, root5Node35Step4Chunk0_2_checked, root5Node35Step4Chunk0_3_checked, root5Node35Step4Chunk0_4_checked, root5Node35Step4Chunk0_5_checked, root5Node35Step4Chunk1_0_checked, root5Node35Step4Chunk1_1_checked, root5Node35Step4Chunk1_2_checked, root5Node35Step4Chunk1_3_checked, root5Node35Step4Chunk1_4_checked, root5Node35Step4Chunk1_5_checked, root5Node35Step4Chunk2_0_checked, root5Node35Step4Chunk2_1_checked, root5Node35Step4Chunk2_2_checked, root5Node35Step4Chunk2_3_checked, root5Node35Step4Chunk2_4_checked, root5Node35Step4Chunk2_5_checked, root5Node35Step4Chunk3_0_checked, root5Node35Step4Chunk3_1_checked, root5Node35Step4Chunk3_2_checked, root5Node35Step4Chunk3_3_checked, root5Node35Step4Chunk3_4_checked, root5Node35Step4Chunk3_5_checked, root5Node35Step4Chunk4_0_checked, root5Node35Step4Chunk4_1_checked, root5Node35Step4Chunk4_2_checked, root5Node35Step4Chunk4_3_checked, root5Node35Step4Chunk4_4_checked, root5Node35Step4Chunk4_5_checked, root5Node35Step4Chunk5_0_checked, root5Node35Step4Chunk5_1_checked, root5Node35Step4Chunk5_2_checked, root5Node35Step4Chunk5_3_checked, root5Node35Step4Chunk5_4_checked, root5Node35Step4Chunk5_5_checked, root5Node35Step4Chunk6_0_checked, root5Node35Step4Chunk6_1_checked, root5Node35Step4Chunk6_2_checked, root5Node35Step4Chunk6_3_checked, root5Node35Step4Chunk6_4_checked, root5Node35Step4Chunk6_5_checked, root5Node35Step4Chunk7_0_checked, root5Node35Step4Chunk7_1_checked, root5Node35Step4Chunk7_2_checked, root5Node35Step4Chunk7_3_checked, root5Node35Step4Chunk7_4_checked, root5Node35Step4Chunk7_5_checked, root5Node35Step4Chunk8_0_checked, root5Node35Step4Chunk8_1_checked, root5Node35Step4Chunk8_2_checked, root5Node35Step4Chunk8_3_checked, root5Node35Step4Chunk8_4_checked, root5Node35Step4Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
