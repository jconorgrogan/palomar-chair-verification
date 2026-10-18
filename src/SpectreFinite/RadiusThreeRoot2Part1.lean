module

public import SpectreFinite.RadiusThreeRoot2Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root2Node0Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(0,4)]
  | 5 => [(5,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(2,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(8,0)]
  | 22 => [(7,5)]
  | 23 => [(6,0)]
  | 24 => [(3,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(8,2)]
  | 29 => [(5,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(8,4)]
  | 34 => [(0,0)]
  | 35 => [(7,2)]
  | _ => [(4,0)]
def root2Node0Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(0,4)]
  | 5 => some [(5,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(2,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(8,0)]
  | 22 => some [(7,5)]
  | 23 => some [(6,0)]
  | 24 => some [(3,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(8,2)]
  | 29 => some [(5,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(8,4)]
  | 34 => some [(0,0)]
  | 35 => some [(7,2)]
  | _ => some [(4,0)]
theorem root2Node0Domains4_fast_eq : root2Node0Domains4 = expandDomains root2Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root2Node0Domains4 v = expandDomains root2Node0Domains4Fast v from by decide) v
theorem root2Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root2Node0Domains3 root2Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root2Node0Domains3 root2Node0Domains4
    root2Node0Domains3Fast root2Node0Domains4Fast
    root2Node0Domains3_fast_eq root2Node0Domains4_fast_eq (by decide)
theorem root2Node0Step4_checked :
    checkReplacement table22 root2Node0Domains3 root2Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root2Node0Step4Chunk0_0_checked, root2Node0Step4Chunk0_1_checked, root2Node0Step4Chunk0_2_checked, root2Node0Step4Chunk0_3_checked, root2Node0Step4Chunk0_4_checked, root2Node0Step4Chunk0_5_checked, root2Node0Step4Chunk1_0_checked, root2Node0Step4Chunk1_1_checked, root2Node0Step4Chunk1_2_checked, root2Node0Step4Chunk1_3_checked, root2Node0Step4Chunk1_4_checked, root2Node0Step4Chunk1_5_checked, root2Node0Step4Chunk2_0_checked, root2Node0Step4Chunk2_1_checked, root2Node0Step4Chunk2_2_checked, root2Node0Step4Chunk2_3_checked, root2Node0Step4Chunk2_4_checked, root2Node0Step4Chunk2_5_checked, root2Node0Step4Chunk3_0_checked, root2Node0Step4Chunk3_1_checked, root2Node0Step4Chunk3_2_checked, root2Node0Step4Chunk3_3_checked, root2Node0Step4Chunk3_4_checked, root2Node0Step4Chunk3_5_checked, root2Node0Step4Chunk4_0_checked, root2Node0Step4Chunk4_1_checked, root2Node0Step4Chunk4_2_checked, root2Node0Step4Chunk4_3_checked, root2Node0Step4Chunk4_4_checked, root2Node0Step4Chunk4_5_checked, root2Node0Step4Chunk5_0_checked, root2Node0Step4Chunk5_1_checked, root2Node0Step4Chunk5_2_checked, root2Node0Step4Chunk5_3_checked, root2Node0Step4Chunk5_4_checked, root2Node0Step4Chunk5_5_checked, root2Node0Step4Chunk6_0_checked, root2Node0Step4Chunk6_1_checked, root2Node0Step4Chunk6_2_checked, root2Node0Step4Chunk6_3_checked, root2Node0Step4Chunk6_4_checked, root2Node0Step4Chunk6_5_checked, root2Node0Step4Chunk7_0_checked, root2Node0Step4Chunk7_1_checked, root2Node0Step4Chunk7_2_checked, root2Node0Step4Chunk7_3_checked, root2Node0Step4Chunk7_4_checked, root2Node0Step4Chunk7_5_checked, root2Node0Step4Chunk8_0_checked, root2Node0Step4Chunk8_1_checked, root2Node0Step4Chunk8_2_checked, root2Node0Step4Chunk8_3_checked, root2Node0Step4Chunk8_4_checked, root2Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
theorem root2Node0Leaf_checked :
    checkCover 1 constraints root2Outputs root2Node0Domains4 (.output 0) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
