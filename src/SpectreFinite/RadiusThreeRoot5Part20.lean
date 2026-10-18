module

public import SpectreFinite.RadiusThreeRoot5Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node35Domains5 (v : Fin 37) : List State :=
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
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(8,1)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node35Domains5Fast (v : Fin 37) : Option (List State) :=
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
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node35Domains5_fast_eq : root5Node35Domains5 = expandDomains root5Node35Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node35Domains5 v = expandDomains root5Node35Domains5Fast v from by decide) v
theorem root5Node35Step5Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root5Node35Domains4 root5Node35Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains4 root5Node35Domains5
    root5Node35Domains4Fast root5Node35Domains5Fast
    root5Node35Domains4_fast_eq root5Node35Domains5_fast_eq (by decide)
theorem root5Node35Step5_checked :
    checkReplacement table22 root5Node35Domains4 root5Node35Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node35Step5Chunk0_0_checked, root5Node35Step5Chunk0_1_checked, root5Node35Step5Chunk0_2_checked, root5Node35Step5Chunk0_3_checked, root5Node35Step5Chunk0_4_checked, root5Node35Step5Chunk0_5_checked, root5Node35Step5Chunk1_0_checked, root5Node35Step5Chunk1_1_checked, root5Node35Step5Chunk1_2_checked, root5Node35Step5Chunk1_3_checked, root5Node35Step5Chunk1_4_checked, root5Node35Step5Chunk1_5_checked, root5Node35Step5Chunk2_0_checked, root5Node35Step5Chunk2_1_checked, root5Node35Step5Chunk2_2_checked, root5Node35Step5Chunk2_3_checked, root5Node35Step5Chunk2_4_checked, root5Node35Step5Chunk2_5_checked, root5Node35Step5Chunk3_0_checked, root5Node35Step5Chunk3_1_checked, root5Node35Step5Chunk3_2_checked, root5Node35Step5Chunk3_3_checked, root5Node35Step5Chunk3_4_checked, root5Node35Step5Chunk3_5_checked, root5Node35Step5Chunk4_0_checked, root5Node35Step5Chunk4_1_checked, root5Node35Step5Chunk4_2_checked, root5Node35Step5Chunk4_3_checked, root5Node35Step5Chunk4_4_checked, root5Node35Step5Chunk4_5_checked, root5Node35Step5Chunk5_0_checked, root5Node35Step5Chunk5_1_checked, root5Node35Step5Chunk5_2_checked, root5Node35Step5Chunk5_3_checked, root5Node35Step5Chunk5_4_checked, root5Node35Step5Chunk5_5_checked, root5Node35Step5Chunk6_0_checked, root5Node35Step5Chunk6_1_checked, root5Node35Step5Chunk6_2_checked, root5Node35Step5Chunk6_3_checked, root5Node35Step5Chunk6_4_checked, root5Node35Step5Chunk6_5_checked, root5Node35Step5Chunk7_0_checked, root5Node35Step5Chunk7_1_checked, root5Node35Step5Chunk7_2_checked, root5Node35Step5Chunk7_3_checked, root5Node35Step5Chunk7_4_checked, root5Node35Step5Chunk7_5_checked, root5Node35Step5Chunk8_0_checked, root5Node35Step5Chunk8_1_checked, root5Node35Step5Chunk8_2_checked, root5Node35Step5Chunk8_3_checked, root5Node35Step5Chunk8_4_checked, root5Node35Step5Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node36Domains0 : Domains 37 State := restrict root5Node35Domains5 3 (1,0)
def root5Node36Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
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
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node36Domains0_fast_eq : root5Node36Domains0 = expandDomains root5Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node36Domains0 v = expandDomains root5Node36Domains0Fast v from by decide) v
theorem root5Node36Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node36Domains0 (.output 17) = true := by decide
def root5Node37Domains0 : Domains 37 State := restrict root5Node35Domains5 3 (3,0)
def root5Node37Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
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
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(8,1)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node37Domains0_fast_eq : root5Node37Domains0 = expandDomains root5Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node37Domains0 v = expandDomains root5Node37Domains0Fast v from by decide) v
theorem root5Node37Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node37Domains0 (.output 18) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
