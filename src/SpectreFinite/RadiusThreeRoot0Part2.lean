module

public import SpectreFinite.RadiusThreeRoot0Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node1Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,3)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(1,3),(7,3),(8,3)]
  | 10 => [(5,5)]
  | 11 => [(1,0)]
  | 12 => [(2,1)]
  | 13 => [(0,2)]
  | 14 => [(1,1)]
  | 15 => [(0,1),(1,4),(6,4),(6,5)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0)]
  | 21 => [(7,3)]
  | 22 => [(6,0)]
  | 23 => [(7,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(0,0)]
  | 34 => [(7,2)]
  | 35 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root0Node1Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(4,2)]
  | 3 => some [(5,3)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(1,3),(7,3),(8,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,0)]
  | 12 => some [(2,1)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,3)]
  | 22 => some [(6,0)]
  | 23 => some [(7,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(0,0)]
  | 34 => some [(7,2)]
  | 35 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root0Node1Domains3_fast_eq : root0Node1Domains3 = expandDomains root0Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node1Domains3 v = expandDomains root0Node1Domains3Fast v from by decide) v
theorem root0Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3_checked :
    checkReplacement table26 root0Node1Domains2 root0Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step3Chunk0_0_checked, root0Node1Step3Chunk0_1_checked, root0Node1Step3Chunk0_2_checked, root0Node1Step3Chunk0_3_checked, root0Node1Step3Chunk0_4_checked, root0Node1Step3Chunk0_5_checked, root0Node1Step3Chunk1_0_checked, root0Node1Step3Chunk1_1_checked, root0Node1Step3Chunk1_2_checked, root0Node1Step3Chunk1_3_checked, root0Node1Step3Chunk1_4_checked, root0Node1Step3Chunk1_5_checked, root0Node1Step3Chunk2_0_checked, root0Node1Step3Chunk2_1_checked, root0Node1Step3Chunk2_2_checked, root0Node1Step3Chunk2_3_checked, root0Node1Step3Chunk2_4_checked, root0Node1Step3Chunk2_5_checked, root0Node1Step3Chunk3_0_checked, root0Node1Step3Chunk3_1_checked, root0Node1Step3Chunk3_2_checked, root0Node1Step3Chunk3_3_checked, root0Node1Step3Chunk3_4_checked, root0Node1Step3Chunk3_5_checked, root0Node1Step3Chunk4_0_checked, root0Node1Step3Chunk4_1_checked, root0Node1Step3Chunk4_2_checked, root0Node1Step3Chunk4_3_checked, root0Node1Step3Chunk4_4_checked, root0Node1Step3Chunk4_5_checked, root0Node1Step3Chunk5_0_checked, root0Node1Step3Chunk5_1_checked, root0Node1Step3Chunk5_2_checked, root0Node1Step3Chunk5_3_checked, root0Node1Step3Chunk5_4_checked, root0Node1Step3Chunk5_5_checked, root0Node1Step3Chunk6_0_checked, root0Node1Step3Chunk6_1_checked, root0Node1Step3Chunk6_2_checked, root0Node1Step3Chunk6_3_checked, root0Node1Step3Chunk6_4_checked, root0Node1Step3Chunk6_5_checked, root0Node1Step3Chunk7_0_checked, root0Node1Step3Chunk7_1_checked, root0Node1Step3Chunk7_2_checked, root0Node1Step3Chunk7_3_checked, root0Node1Step3Chunk7_4_checked, root0Node1Step3Chunk7_5_checked, root0Node1Step3Chunk8_0_checked, root0Node1Step3Chunk8_1_checked, root0Node1Step3Chunk8_2_checked, root0Node1Step3Chunk8_3_checked, root0Node1Step3Chunk8_4_checked, root0Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node1Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(4,2)]
  | 3 => [(5,3)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(8,3)]
  | 10 => [(5,5)]
  | 11 => [(1,0)]
  | 12 => [(2,1)]
  | 13 => [(0,2)]
  | 14 => [(1,1)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0)]
  | 21 => [(7,3)]
  | 22 => [(6,0)]
  | 23 => [(7,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(0,0)]
  | 34 => [(7,2)]
  | 35 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root0Node1Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(4,2)]
  | 3 => some [(5,3)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(8,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,0)]
  | 12 => some [(2,1)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,3)]
  | 22 => some [(6,0)]
  | 23 => some [(7,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(0,0)]
  | 34 => some [(7,2)]
  | 35 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root0Node1Domains4_fast_eq : root0Node1Domains4 = expandDomains root0Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node1Domains4 v = expandDomains root0Node1Domains4Fast v from by decide) v
theorem root0Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4_checked :
    checkReplacement table4 root0Node1Domains3 root0Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step4Chunk0_0_checked, root0Node1Step4Chunk0_1_checked, root0Node1Step4Chunk0_2_checked, root0Node1Step4Chunk0_3_checked, root0Node1Step4Chunk0_4_checked, root0Node1Step4Chunk0_5_checked, root0Node1Step4Chunk1_0_checked, root0Node1Step4Chunk1_1_checked, root0Node1Step4Chunk1_2_checked, root0Node1Step4Chunk1_3_checked, root0Node1Step4Chunk1_4_checked, root0Node1Step4Chunk1_5_checked, root0Node1Step4Chunk2_0_checked, root0Node1Step4Chunk2_1_checked, root0Node1Step4Chunk2_2_checked, root0Node1Step4Chunk2_3_checked, root0Node1Step4Chunk2_4_checked, root0Node1Step4Chunk2_5_checked, root0Node1Step4Chunk3_0_checked, root0Node1Step4Chunk3_1_checked, root0Node1Step4Chunk3_2_checked, root0Node1Step4Chunk3_3_checked, root0Node1Step4Chunk3_4_checked, root0Node1Step4Chunk3_5_checked, root0Node1Step4Chunk4_0_checked, root0Node1Step4Chunk4_1_checked, root0Node1Step4Chunk4_2_checked, root0Node1Step4Chunk4_3_checked, root0Node1Step4Chunk4_4_checked, root0Node1Step4Chunk4_5_checked, root0Node1Step4Chunk5_0_checked, root0Node1Step4Chunk5_1_checked, root0Node1Step4Chunk5_2_checked, root0Node1Step4Chunk5_3_checked, root0Node1Step4Chunk5_4_checked, root0Node1Step4Chunk5_5_checked, root0Node1Step4Chunk6_0_checked, root0Node1Step4Chunk6_1_checked, root0Node1Step4Chunk6_2_checked, root0Node1Step4Chunk6_3_checked, root0Node1Step4Chunk6_4_checked, root0Node1Step4Chunk6_5_checked, root0Node1Step4Chunk7_0_checked, root0Node1Step4Chunk7_1_checked, root0Node1Step4Chunk7_2_checked, root0Node1Step4Chunk7_3_checked, root0Node1Step4Chunk7_4_checked, root0Node1Step4Chunk7_5_checked, root0Node1Step4Chunk8_0_checked, root0Node1Step4Chunk8_1_checked, root0Node1Step4Chunk8_2_checked, root0Node1Step4Chunk8_3_checked, root0Node1Step4Chunk8_4_checked, root0Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node2Domains0 : Domains 37 State := restrict root0Node1Domains4 36 (1,3)
def root0Node2Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(4,2)]
  | 3 => some [(5,3)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(8,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,0)]
  | 12 => some [(2,1)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,3)]
  | 22 => some [(6,0)]
  | 23 => some [(7,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(0,0)]
  | 34 => some [(7,2)]
  | 35 => some [(7,4)]
  | _ => some [(1,3)]
theorem root0Node2Domains0_fast_eq : root0Node2Domains0 = expandDomains root0Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node2Domains0 v = expandDomains root0Node2Domains0Fast v from by decide) v
theorem root0Node2Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node2Domains0 (.output 0) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
