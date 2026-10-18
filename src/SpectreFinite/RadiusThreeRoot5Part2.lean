module

public import SpectreFinite.RadiusThreeRoot5Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node1Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(4,2),(5,2),(5,5),(8,2)]
  | 3 => [(1,0),(3,0),(5,0),(5,3)]
  | 4 => [(5,1),(5,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3)]
  | 9 => [(4,3),(5,3),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5),(6,5)]
  | 14 => [(0,4),(6,1)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3),(8,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node1Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(4,2),(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0),(5,3)]
  | 4 => some [(5,1),(5,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3)]
  | 9 => some [(4,3),(5,3),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node1Domains3_fast_eq : root5Node1Domains3 = expandDomains root5Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node1Domains3 v = expandDomains root5Node1Domains3Fast v from by decide) v
theorem root5Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3_checked :
    checkReplacement table13 root5Node1Domains2 root5Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step3Chunk0_0_checked, root5Node1Step3Chunk0_1_checked, root5Node1Step3Chunk0_2_checked, root5Node1Step3Chunk0_3_checked, root5Node1Step3Chunk0_4_checked, root5Node1Step3Chunk0_5_checked, root5Node1Step3Chunk1_0_checked, root5Node1Step3Chunk1_1_checked, root5Node1Step3Chunk1_2_checked, root5Node1Step3Chunk1_3_checked, root5Node1Step3Chunk1_4_checked, root5Node1Step3Chunk1_5_checked, root5Node1Step3Chunk2_0_checked, root5Node1Step3Chunk2_1_checked, root5Node1Step3Chunk2_2_checked, root5Node1Step3Chunk2_3_checked, root5Node1Step3Chunk2_4_checked, root5Node1Step3Chunk2_5_checked, root5Node1Step3Chunk3_0_checked, root5Node1Step3Chunk3_1_checked, root5Node1Step3Chunk3_2_checked, root5Node1Step3Chunk3_3_checked, root5Node1Step3Chunk3_4_checked, root5Node1Step3Chunk3_5_checked, root5Node1Step3Chunk4_0_checked, root5Node1Step3Chunk4_1_checked, root5Node1Step3Chunk4_2_checked, root5Node1Step3Chunk4_3_checked, root5Node1Step3Chunk4_4_checked, root5Node1Step3Chunk4_5_checked, root5Node1Step3Chunk5_0_checked, root5Node1Step3Chunk5_1_checked, root5Node1Step3Chunk5_2_checked, root5Node1Step3Chunk5_3_checked, root5Node1Step3Chunk5_4_checked, root5Node1Step3Chunk5_5_checked, root5Node1Step3Chunk6_0_checked, root5Node1Step3Chunk6_1_checked, root5Node1Step3Chunk6_2_checked, root5Node1Step3Chunk6_3_checked, root5Node1Step3Chunk6_4_checked, root5Node1Step3Chunk6_5_checked, root5Node1Step3Chunk7_0_checked, root5Node1Step3Chunk7_1_checked, root5Node1Step3Chunk7_2_checked, root5Node1Step3Chunk7_3_checked, root5Node1Step3Chunk7_4_checked, root5Node1Step3Chunk7_5_checked, root5Node1Step3Chunk8_0_checked, root5Node1Step3Chunk8_1_checked, root5Node1Step3Chunk8_2_checked, root5Node1Step3Chunk8_3_checked, root5Node1Step3Chunk8_4_checked, root5Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node1Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(4,2),(5,2),(5,5),(8,2)]
  | 3 => [(1,0),(3,0),(5,0),(5,3)]
  | 4 => [(5,1),(5,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3)]
  | 9 => [(4,3),(5,3),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5),(6,5)]
  | 14 => [(0,4),(6,1)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3),(8,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(2,0)]
  | _ => [(7,3)]
def root5Node1Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(4,2),(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0),(5,3)]
  | 4 => some [(5,1),(5,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3)]
  | 9 => some [(4,3),(5,3),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node1Domains4_fast_eq : root5Node1Domains4 = expandDomains root5Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node1Domains4 v = expandDomains root5Node1Domains4Fast v from by decide) v
theorem root5Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4_checked :
    checkReplacement table25 root5Node1Domains3 root5Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step4Chunk0_0_checked, root5Node1Step4Chunk0_1_checked, root5Node1Step4Chunk0_2_checked, root5Node1Step4Chunk0_3_checked, root5Node1Step4Chunk0_4_checked, root5Node1Step4Chunk0_5_checked, root5Node1Step4Chunk1_0_checked, root5Node1Step4Chunk1_1_checked, root5Node1Step4Chunk1_2_checked, root5Node1Step4Chunk1_3_checked, root5Node1Step4Chunk1_4_checked, root5Node1Step4Chunk1_5_checked, root5Node1Step4Chunk2_0_checked, root5Node1Step4Chunk2_1_checked, root5Node1Step4Chunk2_2_checked, root5Node1Step4Chunk2_3_checked, root5Node1Step4Chunk2_4_checked, root5Node1Step4Chunk2_5_checked, root5Node1Step4Chunk3_0_checked, root5Node1Step4Chunk3_1_checked, root5Node1Step4Chunk3_2_checked, root5Node1Step4Chunk3_3_checked, root5Node1Step4Chunk3_4_checked, root5Node1Step4Chunk3_5_checked, root5Node1Step4Chunk4_0_checked, root5Node1Step4Chunk4_1_checked, root5Node1Step4Chunk4_2_checked, root5Node1Step4Chunk4_3_checked, root5Node1Step4Chunk4_4_checked, root5Node1Step4Chunk4_5_checked, root5Node1Step4Chunk5_0_checked, root5Node1Step4Chunk5_1_checked, root5Node1Step4Chunk5_2_checked, root5Node1Step4Chunk5_3_checked, root5Node1Step4Chunk5_4_checked, root5Node1Step4Chunk5_5_checked, root5Node1Step4Chunk6_0_checked, root5Node1Step4Chunk6_1_checked, root5Node1Step4Chunk6_2_checked, root5Node1Step4Chunk6_3_checked, root5Node1Step4Chunk6_4_checked, root5Node1Step4Chunk6_5_checked, root5Node1Step4Chunk7_0_checked, root5Node1Step4Chunk7_1_checked, root5Node1Step4Chunk7_2_checked, root5Node1Step4Chunk7_3_checked, root5Node1Step4Chunk7_4_checked, root5Node1Step4Chunk7_5_checked, root5Node1Step4Chunk8_0_checked, root5Node1Step4Chunk8_1_checked, root5Node1Step4Chunk8_2_checked, root5Node1Step4Chunk8_3_checked, root5Node1Step4Chunk8_4_checked, root5Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node2Domains0 : Domains 37 State := restrict root5Node1Domains4 0 (4,0)
def root5Node2Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(4,2),(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0),(5,3)]
  | 4 => some [(5,1),(5,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3)]
  | 9 => some [(4,3),(5,3),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node2Domains0_fast_eq : root5Node2Domains0 = expandDomains root5Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node2Domains0 v = expandDomains root5Node2Domains0Fast v from by decide) v
def root5Node2Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2),(5,2),(8,2)]
  | 3 => [(5,0),(5,3)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(7,4),(8,4)]
  | 8 => [(0,0),(1,3)]
  | 9 => [(4,3),(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5),(6,5)]
  | 14 => [(0,4),(6,1)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(7,0)]
  | 21 => [(4,3),(8,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(2,0)]
  | _ => [(7,3)]
def root5Node2Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(4,2),(5,2),(8,2)]
  | 3 => some [(5,0),(5,3)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3)]
  | 9 => some [(4,3),(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(7,0)]
  | 21 => some [(4,3),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0)]
  | _ => some [(7,3)]
theorem root5Node2Domains1_fast_eq : root5Node2Domains1 = expandDomains root5Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node2Domains1 v = expandDomains root5Node2Domains1Fast v from by decide) v
theorem root5Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1_checked :
    checkReplacement table1 root5Node2Domains0 root5Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node2Step1Chunk0_0_checked, root5Node2Step1Chunk0_1_checked, root5Node2Step1Chunk0_2_checked, root5Node2Step1Chunk0_3_checked, root5Node2Step1Chunk0_4_checked, root5Node2Step1Chunk0_5_checked, root5Node2Step1Chunk1_0_checked, root5Node2Step1Chunk1_1_checked, root5Node2Step1Chunk1_2_checked, root5Node2Step1Chunk1_3_checked, root5Node2Step1Chunk1_4_checked, root5Node2Step1Chunk1_5_checked, root5Node2Step1Chunk2_0_checked, root5Node2Step1Chunk2_1_checked, root5Node2Step1Chunk2_2_checked, root5Node2Step1Chunk2_3_checked, root5Node2Step1Chunk2_4_checked, root5Node2Step1Chunk2_5_checked, root5Node2Step1Chunk3_0_checked, root5Node2Step1Chunk3_1_checked, root5Node2Step1Chunk3_2_checked, root5Node2Step1Chunk3_3_checked, root5Node2Step1Chunk3_4_checked, root5Node2Step1Chunk3_5_checked, root5Node2Step1Chunk4_0_checked, root5Node2Step1Chunk4_1_checked, root5Node2Step1Chunk4_2_checked, root5Node2Step1Chunk4_3_checked, root5Node2Step1Chunk4_4_checked, root5Node2Step1Chunk4_5_checked, root5Node2Step1Chunk5_0_checked, root5Node2Step1Chunk5_1_checked, root5Node2Step1Chunk5_2_checked, root5Node2Step1Chunk5_3_checked, root5Node2Step1Chunk5_4_checked, root5Node2Step1Chunk5_5_checked, root5Node2Step1Chunk6_0_checked, root5Node2Step1Chunk6_1_checked, root5Node2Step1Chunk6_2_checked, root5Node2Step1Chunk6_3_checked, root5Node2Step1Chunk6_4_checked, root5Node2Step1Chunk6_5_checked, root5Node2Step1Chunk7_0_checked, root5Node2Step1Chunk7_1_checked, root5Node2Step1Chunk7_2_checked, root5Node2Step1Chunk7_3_checked, root5Node2Step1Chunk7_4_checked, root5Node2Step1Chunk7_5_checked, root5Node2Step1Chunk8_0_checked, root5Node2Step1Chunk8_1_checked, root5Node2Step1Chunk8_2_checked, root5Node2Step1Chunk8_3_checked, root5Node2Step1Chunk8_4_checked, root5Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
