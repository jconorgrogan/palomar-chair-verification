module

public import SpectreFinite.RadiusThreeRoot5Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node0Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => [(0,1),(1,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(3,3),(7,3)]
  | 9 => [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(4,1),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(3,1),(7,1)]
  | 13 => [(0,1),(1,5),(6,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(4,0),(7,0),(7,4),(8,0)]
  | 16 => [(1,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1),(6,4),(6,5)]
  | 23 => [(0,4),(1,2),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0),(7,0)]
  | 29 => [(4,3),(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(1,4),(5,0),(5,3)]
  | 34 => [(0,5),(4,5),(5,5),(8,5)]
  | 35 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node0Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(7,4),(8,0)]
  | 16 => some [(1,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4),(6,5)]
  | 23 => some [(0,4),(1,2),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0),(7,0)]
  | 29 => some [(4,3),(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(1,4),(5,0),(5,3)]
  | 34 => some [(0,5),(4,5),(5,5),(8,5)]
  | 35 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node0Domains4_fast_eq : root5Node0Domains4 = expandDomains root5Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node0Domains4 v = expandDomains root5Node0Domains4Fast v from by decide) v
theorem root5Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node0Domains3 root5Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node0Domains3 root5Node0Domains4
    root5Node0Domains3Fast root5Node0Domains4Fast
    root5Node0Domains3_fast_eq root5Node0Domains4_fast_eq (by decide)
theorem root5Node0Step4_checked :
    checkReplacement table23 root5Node0Domains3 root5Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node0Step4Chunk0_0_checked, root5Node0Step4Chunk0_1_checked, root5Node0Step4Chunk0_2_checked, root5Node0Step4Chunk0_3_checked, root5Node0Step4Chunk0_4_checked, root5Node0Step4Chunk0_5_checked, root5Node0Step4Chunk1_0_checked, root5Node0Step4Chunk1_1_checked, root5Node0Step4Chunk1_2_checked, root5Node0Step4Chunk1_3_checked, root5Node0Step4Chunk1_4_checked, root5Node0Step4Chunk1_5_checked, root5Node0Step4Chunk2_0_checked, root5Node0Step4Chunk2_1_checked, root5Node0Step4Chunk2_2_checked, root5Node0Step4Chunk2_3_checked, root5Node0Step4Chunk2_4_checked, root5Node0Step4Chunk2_5_checked, root5Node0Step4Chunk3_0_checked, root5Node0Step4Chunk3_1_checked, root5Node0Step4Chunk3_2_checked, root5Node0Step4Chunk3_3_checked, root5Node0Step4Chunk3_4_checked, root5Node0Step4Chunk3_5_checked, root5Node0Step4Chunk4_0_checked, root5Node0Step4Chunk4_1_checked, root5Node0Step4Chunk4_2_checked, root5Node0Step4Chunk4_3_checked, root5Node0Step4Chunk4_4_checked, root5Node0Step4Chunk4_5_checked, root5Node0Step4Chunk5_0_checked, root5Node0Step4Chunk5_1_checked, root5Node0Step4Chunk5_2_checked, root5Node0Step4Chunk5_3_checked, root5Node0Step4Chunk5_4_checked, root5Node0Step4Chunk5_5_checked, root5Node0Step4Chunk6_0_checked, root5Node0Step4Chunk6_1_checked, root5Node0Step4Chunk6_2_checked, root5Node0Step4Chunk6_3_checked, root5Node0Step4Chunk6_4_checked, root5Node0Step4Chunk6_5_checked, root5Node0Step4Chunk7_0_checked, root5Node0Step4Chunk7_1_checked, root5Node0Step4Chunk7_2_checked, root5Node0Step4Chunk7_3_checked, root5Node0Step4Chunk7_4_checked, root5Node0Step4Chunk7_5_checked, root5Node0Step4Chunk8_0_checked, root5Node0Step4Chunk8_1_checked, root5Node0Step4Chunk8_2_checked, root5Node0Step4Chunk8_3_checked, root5Node0Step4Chunk8_4_checked, root5Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node1Domains0 : Domains 37 State := restrict root5Node0Domains4 16 (1,3)
def root5Node1Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(7,4),(8,0)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4),(6,5)]
  | 23 => some [(0,4),(1,2),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0),(7,0)]
  | 29 => some [(4,3),(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(1,4),(5,0),(5,3)]
  | 34 => some [(0,5),(4,5),(5,5),(8,5)]
  | 35 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node1Domains0_fast_eq : root5Node1Domains0 = expandDomains root5Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node1Domains0 v = expandDomains root5Node1Domains0Fast v from by decide) v
def root5Node1Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(4,2),(5,2),(5,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => [(5,1),(5,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(3,3),(7,3)]
  | 9 => [(4,3),(5,3),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5),(6,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(4,0),(7,0),(7,4),(8,0)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1),(6,4),(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0),(7,0)]
  | 29 => [(4,3),(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(1,4),(5,0),(5,3)]
  | 34 => [(0,5),(4,5),(5,5),(8,5)]
  | 35 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node1Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(4,2),(5,2),(5,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => some [(5,1),(5,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(4,3),(5,3),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(7,4),(8,0)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4),(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0),(7,0)]
  | 29 => some [(4,3),(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(1,4),(5,0),(5,3)]
  | 34 => some [(0,5),(4,5),(5,5),(8,5)]
  | 35 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node1Domains1_fast_eq : root5Node1Domains1 = expandDomains root5Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node1Domains1 v = expandDomains root5Node1Domains1Fast v from by decide) v
theorem root5Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1_checked :
    checkReplacement table11 root5Node1Domains0 root5Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step1Chunk0_0_checked, root5Node1Step1Chunk0_1_checked, root5Node1Step1Chunk0_2_checked, root5Node1Step1Chunk0_3_checked, root5Node1Step1Chunk0_4_checked, root5Node1Step1Chunk0_5_checked, root5Node1Step1Chunk1_0_checked, root5Node1Step1Chunk1_1_checked, root5Node1Step1Chunk1_2_checked, root5Node1Step1Chunk1_3_checked, root5Node1Step1Chunk1_4_checked, root5Node1Step1Chunk1_5_checked, root5Node1Step1Chunk2_0_checked, root5Node1Step1Chunk2_1_checked, root5Node1Step1Chunk2_2_checked, root5Node1Step1Chunk2_3_checked, root5Node1Step1Chunk2_4_checked, root5Node1Step1Chunk2_5_checked, root5Node1Step1Chunk3_0_checked, root5Node1Step1Chunk3_1_checked, root5Node1Step1Chunk3_2_checked, root5Node1Step1Chunk3_3_checked, root5Node1Step1Chunk3_4_checked, root5Node1Step1Chunk3_5_checked, root5Node1Step1Chunk4_0_checked, root5Node1Step1Chunk4_1_checked, root5Node1Step1Chunk4_2_checked, root5Node1Step1Chunk4_3_checked, root5Node1Step1Chunk4_4_checked, root5Node1Step1Chunk4_5_checked, root5Node1Step1Chunk5_0_checked, root5Node1Step1Chunk5_1_checked, root5Node1Step1Chunk5_2_checked, root5Node1Step1Chunk5_3_checked, root5Node1Step1Chunk5_4_checked, root5Node1Step1Chunk5_5_checked, root5Node1Step1Chunk6_0_checked, root5Node1Step1Chunk6_1_checked, root5Node1Step1Chunk6_2_checked, root5Node1Step1Chunk6_3_checked, root5Node1Step1Chunk6_4_checked, root5Node1Step1Chunk6_5_checked, root5Node1Step1Chunk7_0_checked, root5Node1Step1Chunk7_1_checked, root5Node1Step1Chunk7_2_checked, root5Node1Step1Chunk7_3_checked, root5Node1Step1Chunk7_4_checked, root5Node1Step1Chunk7_5_checked, root5Node1Step1Chunk8_0_checked, root5Node1Step1Chunk8_1_checked, root5Node1Step1Chunk8_2_checked, root5Node1Step1Chunk8_3_checked, root5Node1Step1Chunk8_4_checked, root5Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node1Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(4,2),(5,2),(5,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => [(5,1),(5,4)]
  | 5 => [(0,1),(1,4)]
  | 6 => [(0,5),(6,2)]
  | 7 => [(4,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(3,3),(7,3)]
  | 9 => [(4,3),(5,3),(8,3)]
  | 10 => [(7,5),(8,5)]
  | 11 => [(1,0),(6,0)]
  | 12 => [(7,1)]
  | 13 => [(1,5),(6,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node1Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(4,2),(5,2),(5,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(5,3),(6,1)]
  | 4 => some [(5,1),(5,4)]
  | 5 => some [(0,1),(1,4)]
  | 6 => some [(0,5),(6,2)]
  | 7 => some [(4,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(4,3),(5,3),(8,3)]
  | 10 => some [(7,5),(8,5)]
  | 11 => some [(1,0),(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node1Domains2_fast_eq : root5Node1Domains2 = expandDomains root5Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node1Domains2 v = expandDomains root5Node1Domains2Fast v from by decide) v
theorem root5Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2_checked :
    checkReplacement table23 root5Node1Domains1 root5Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step2Chunk0_0_checked, root5Node1Step2Chunk0_1_checked, root5Node1Step2Chunk0_2_checked, root5Node1Step2Chunk0_3_checked, root5Node1Step2Chunk0_4_checked, root5Node1Step2Chunk0_5_checked, root5Node1Step2Chunk1_0_checked, root5Node1Step2Chunk1_1_checked, root5Node1Step2Chunk1_2_checked, root5Node1Step2Chunk1_3_checked, root5Node1Step2Chunk1_4_checked, root5Node1Step2Chunk1_5_checked, root5Node1Step2Chunk2_0_checked, root5Node1Step2Chunk2_1_checked, root5Node1Step2Chunk2_2_checked, root5Node1Step2Chunk2_3_checked, root5Node1Step2Chunk2_4_checked, root5Node1Step2Chunk2_5_checked, root5Node1Step2Chunk3_0_checked, root5Node1Step2Chunk3_1_checked, root5Node1Step2Chunk3_2_checked, root5Node1Step2Chunk3_3_checked, root5Node1Step2Chunk3_4_checked, root5Node1Step2Chunk3_5_checked, root5Node1Step2Chunk4_0_checked, root5Node1Step2Chunk4_1_checked, root5Node1Step2Chunk4_2_checked, root5Node1Step2Chunk4_3_checked, root5Node1Step2Chunk4_4_checked, root5Node1Step2Chunk4_5_checked, root5Node1Step2Chunk5_0_checked, root5Node1Step2Chunk5_1_checked, root5Node1Step2Chunk5_2_checked, root5Node1Step2Chunk5_3_checked, root5Node1Step2Chunk5_4_checked, root5Node1Step2Chunk5_5_checked, root5Node1Step2Chunk6_0_checked, root5Node1Step2Chunk6_1_checked, root5Node1Step2Chunk6_2_checked, root5Node1Step2Chunk6_3_checked, root5Node1Step2Chunk6_4_checked, root5Node1Step2Chunk6_5_checked, root5Node1Step2Chunk7_0_checked, root5Node1Step2Chunk7_1_checked, root5Node1Step2Chunk7_2_checked, root5Node1Step2Chunk7_3_checked, root5Node1Step2Chunk7_4_checked, root5Node1Step2Chunk7_5_checked, root5Node1Step2Chunk8_0_checked, root5Node1Step2Chunk8_1_checked, root5Node1Step2Chunk8_2_checked, root5Node1Step2Chunk8_3_checked, root5Node1Step2Chunk8_4_checked, root5Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
