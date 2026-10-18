module

public import SpectreFinite.RadiusThreeRoot0Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node5Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(4,2)]
  | 3 => [(5,3)]
  | 4 => [(8,1)]
  | 5 => [(6,5)]
  | 6 => [(0,4)]
  | 7 => [(1,4)]
  | 8 => [(0,5)]
  | 9 => [(8,3)]
  | 10 => [(5,5)]
  | 11 => [(3,0)]
  | 12 => [(2,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
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
def root0Node5Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(4,2)]
  | 3 => some [(5,3)]
  | 4 => some [(8,1)]
  | 5 => some [(6,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(8,3)]
  | 10 => some [(5,5)]
  | 11 => some [(3,0)]
  | 12 => some [(2,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
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
theorem root0Node5Domains4_fast_eq : root0Node5Domains4 = expandDomains root0Node5Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node5Domains4 v = expandDomains root0Node5Domains4Fast v from by decide) v
theorem root0Node5Step4Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root0Node5Domains3 root0Node5Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains3 root0Node5Domains4
    root0Node5Domains3Fast root0Node5Domains4Fast
    root0Node5Domains3_fast_eq root0Node5Domains4_fast_eq (by decide)
theorem root0Node5Step4_checked :
    checkReplacement table4 root0Node5Domains3 root0Node5Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node5Step4Chunk0_0_checked, root0Node5Step4Chunk0_1_checked, root0Node5Step4Chunk0_2_checked, root0Node5Step4Chunk0_3_checked, root0Node5Step4Chunk0_4_checked, root0Node5Step4Chunk0_5_checked, root0Node5Step4Chunk1_0_checked, root0Node5Step4Chunk1_1_checked, root0Node5Step4Chunk1_2_checked, root0Node5Step4Chunk1_3_checked, root0Node5Step4Chunk1_4_checked, root0Node5Step4Chunk1_5_checked, root0Node5Step4Chunk2_0_checked, root0Node5Step4Chunk2_1_checked, root0Node5Step4Chunk2_2_checked, root0Node5Step4Chunk2_3_checked, root0Node5Step4Chunk2_4_checked, root0Node5Step4Chunk2_5_checked, root0Node5Step4Chunk3_0_checked, root0Node5Step4Chunk3_1_checked, root0Node5Step4Chunk3_2_checked, root0Node5Step4Chunk3_3_checked, root0Node5Step4Chunk3_4_checked, root0Node5Step4Chunk3_5_checked, root0Node5Step4Chunk4_0_checked, root0Node5Step4Chunk4_1_checked, root0Node5Step4Chunk4_2_checked, root0Node5Step4Chunk4_3_checked, root0Node5Step4Chunk4_4_checked, root0Node5Step4Chunk4_5_checked, root0Node5Step4Chunk5_0_checked, root0Node5Step4Chunk5_1_checked, root0Node5Step4Chunk5_2_checked, root0Node5Step4Chunk5_3_checked, root0Node5Step4Chunk5_4_checked, root0Node5Step4Chunk5_5_checked, root0Node5Step4Chunk6_0_checked, root0Node5Step4Chunk6_1_checked, root0Node5Step4Chunk6_2_checked, root0Node5Step4Chunk6_3_checked, root0Node5Step4Chunk6_4_checked, root0Node5Step4Chunk6_5_checked, root0Node5Step4Chunk7_0_checked, root0Node5Step4Chunk7_1_checked, root0Node5Step4Chunk7_2_checked, root0Node5Step4Chunk7_3_checked, root0Node5Step4Chunk7_4_checked, root0Node5Step4Chunk7_5_checked, root0Node5Step4Chunk8_0_checked, root0Node5Step4Chunk8_1_checked, root0Node5Step4Chunk8_2_checked, root0Node5Step4Chunk8_3_checked, root0Node5Step4Chunk8_4_checked, root0Node5Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node6Domains0 : Domains 37 State := restrict root0Node5Domains4 36 (1,3)
def root0Node6Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(4,2)]
  | 3 => some [(5,3)]
  | 4 => some [(8,1)]
  | 5 => some [(6,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(8,3)]
  | 10 => some [(5,5)]
  | 11 => some [(3,0)]
  | 12 => some [(2,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
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
theorem root0Node6Domains0_fast_eq : root0Node6Domains0 = expandDomains root0Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node6Domains0 v = expandDomains root0Node6Domains0Fast v from by decide) v
theorem root0Node6Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node6Domains0 (.output 2) = true := by decide
def root0Node7Domains0 : Domains 37 State := restrict root0Node5Domains4 36 (6,3)
def root0Node7Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(4,2)]
  | 3 => some [(5,3)]
  | 4 => some [(8,1)]
  | 5 => some [(6,5)]
  | 6 => some [(0,4)]
  | 7 => some [(1,4)]
  | 8 => some [(0,5)]
  | 9 => some [(8,3)]
  | 10 => some [(5,5)]
  | 11 => some [(3,0)]
  | 12 => some [(2,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
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
  | _ => some [(6,3)]
theorem root0Node7Domains0_fast_eq : root0Node7Domains0 = expandDomains root0Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node7Domains0 v = expandDomains root0Node7Domains0Fast v from by decide) v
theorem root0Node7Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node7Domains0 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
