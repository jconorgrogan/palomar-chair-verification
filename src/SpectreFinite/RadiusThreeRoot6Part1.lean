module

public import SpectreFinite.RadiusThreeRoot6Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable12
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable24

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node0Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5),(7,5)]
  | 1 => [(0,3),(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 4 => [(1,3),(5,2),(5,5)]
  | 5 => [(4,2),(7,0),(8,0)]
  | 6 => [(4,3),(5,3),(8,3)]
  | 7 => [(1,5),(3,5),(5,5)]
  | 8 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 9 => [(0,4),(0,5),(6,2),(6,5)]
  | 10 => [(0,4),(4,4),(5,4),(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0),(2,4),(4,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => [(1,0),(5,5),(6,0),(7,0)]
  | 16 => [(3,0),(4,3),(7,1)]
  | 17 => [(2,5),(7,5)]
  | 18 => [(6,0)]
  | 19 => [(3,1),(7,1)]
  | 20 => [(0,1),(1,5),(6,5),(7,5)]
  | 21 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => [(4,0),(4,4),(7,4),(8,0)]
  | 23 => [(0,0),(1,3),(6,3),(7,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(1,0),(4,2),(7,0),(8,2)]
  | 28 => [(0,1),(0,2),(1,5),(6,4),(6,5)]
  | 29 => [(0,4),(1,1),(1,2),(6,1),(6,2)]
  | 30 => [(5,1),(5,4),(8,4)]
  | 31 => [(0,0),(0,1),(6,4)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(0,3),(1,0),(7,0),(8,0)]
  | 34 => [(4,3),(7,1),(8,1),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root6Node0Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5),(7,5)]
  | 1 => some [(0,3),(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 4 => some [(1,3),(5,2),(5,5)]
  | 5 => some [(4,2),(7,0),(8,0)]
  | 6 => some [(4,3),(5,3),(8,3)]
  | 7 => some [(1,5),(3,5),(5,5)]
  | 8 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 9 => some [(0,4),(0,5),(6,2),(6,5)]
  | 10 => some [(0,4),(4,4),(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4),(4,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => some [(1,0),(5,5),(6,0),(7,0)]
  | 16 => some [(3,0),(4,3),(7,1)]
  | 17 => some [(2,5),(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,0),(4,4),(7,4),(8,0)]
  | 23 => some [(0,0),(1,3),(6,3),(7,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(0,2),(1,5),(6,4),(6,5)]
  | 29 => some [(0,4),(1,1),(1,2),(6,1),(6,2)]
  | 30 => some [(5,1),(5,4),(8,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(0,3),(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,1),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node0Domains4_fast_eq : root6Node0Domains4 = expandDomains root6Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node0Domains4 v = expandDomains root6Node0Domains4Fast v from by decide) v
theorem root6Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node0Domains3 root6Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node0Domains3 root6Node0Domains4
    root6Node0Domains3Fast root6Node0Domains4Fast
    root6Node0Domains3_fast_eq root6Node0Domains4_fast_eq (by decide)
theorem root6Node0Step4_checked :
    checkReplacement table13 root6Node0Domains3 root6Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node0Step4Chunk0_0_checked, root6Node0Step4Chunk0_1_checked, root6Node0Step4Chunk0_2_checked, root6Node0Step4Chunk0_3_checked, root6Node0Step4Chunk0_4_checked, root6Node0Step4Chunk0_5_checked, root6Node0Step4Chunk1_0_checked, root6Node0Step4Chunk1_1_checked, root6Node0Step4Chunk1_2_checked, root6Node0Step4Chunk1_3_checked, root6Node0Step4Chunk1_4_checked, root6Node0Step4Chunk1_5_checked, root6Node0Step4Chunk2_0_checked, root6Node0Step4Chunk2_1_checked, root6Node0Step4Chunk2_2_checked, root6Node0Step4Chunk2_3_checked, root6Node0Step4Chunk2_4_checked, root6Node0Step4Chunk2_5_checked, root6Node0Step4Chunk3_0_checked, root6Node0Step4Chunk3_1_checked, root6Node0Step4Chunk3_2_checked, root6Node0Step4Chunk3_3_checked, root6Node0Step4Chunk3_4_checked, root6Node0Step4Chunk3_5_checked, root6Node0Step4Chunk4_0_checked, root6Node0Step4Chunk4_1_checked, root6Node0Step4Chunk4_2_checked, root6Node0Step4Chunk4_3_checked, root6Node0Step4Chunk4_4_checked, root6Node0Step4Chunk4_5_checked, root6Node0Step4Chunk5_0_checked, root6Node0Step4Chunk5_1_checked, root6Node0Step4Chunk5_2_checked, root6Node0Step4Chunk5_3_checked, root6Node0Step4Chunk5_4_checked, root6Node0Step4Chunk5_5_checked, root6Node0Step4Chunk6_0_checked, root6Node0Step4Chunk6_1_checked, root6Node0Step4Chunk6_2_checked, root6Node0Step4Chunk6_3_checked, root6Node0Step4Chunk6_4_checked, root6Node0Step4Chunk6_5_checked, root6Node0Step4Chunk7_0_checked, root6Node0Step4Chunk7_1_checked, root6Node0Step4Chunk7_2_checked, root6Node0Step4Chunk7_3_checked, root6Node0Step4Chunk7_4_checked, root6Node0Step4Chunk7_5_checked, root6Node0Step4Chunk8_0_checked, root6Node0Step4Chunk8_1_checked, root6Node0Step4Chunk8_2_checked, root6Node0Step4Chunk8_3_checked, root6Node0Step4Chunk8_4_checked, root6Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node1Domains0 : Domains 37 State := restrict root6Node0Domains4 17 (2,5)
def root6Node1Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5),(7,5)]
  | 1 => some [(0,3),(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 4 => some [(1,3),(5,2),(5,5)]
  | 5 => some [(4,2),(7,0),(8,0)]
  | 6 => some [(4,3),(5,3),(8,3)]
  | 7 => some [(1,5),(3,5),(5,5)]
  | 8 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 9 => some [(0,4),(0,5),(6,2),(6,5)]
  | 10 => some [(0,4),(4,4),(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4),(4,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => some [(1,0),(5,5),(6,0),(7,0)]
  | 16 => some [(3,0),(4,3),(7,1)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(3,1),(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,0),(4,4),(7,4),(8,0)]
  | 23 => some [(0,0),(1,3),(6,3),(7,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(0,2),(1,5),(6,4),(6,5)]
  | 29 => some [(0,4),(1,1),(1,2),(6,1),(6,2)]
  | 30 => some [(5,1),(5,4),(8,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(0,3),(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,1),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node1Domains0_fast_eq : root6Node1Domains0 = expandDomains root6Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node1Domains0 v = expandDomains root6Node1Domains0Fast v from by decide) v
def root6Node1Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5),(7,5)]
  | 1 => [(0,3),(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 4 => [(1,3),(5,2),(5,5)]
  | 5 => [(4,2),(7,0),(8,0)]
  | 6 => [(4,3),(5,3),(8,3)]
  | 7 => [(1,5),(3,5),(5,5)]
  | 8 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 9 => [(0,4),(0,5),(6,2),(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0),(2,4),(4,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => [(1,0),(5,5),(6,0),(7,0)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(0,1),(1,5),(6,5),(7,5)]
  | 21 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => [(4,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(1,0),(4,2),(7,0),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root6Node1Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5),(7,5)]
  | 1 => some [(0,3),(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 4 => some [(1,3),(5,2),(5,5)]
  | 5 => some [(4,2),(7,0),(8,0)]
  | 6 => some [(4,3),(5,3),(8,3)]
  | 7 => some [(1,5),(3,5),(5,5)]
  | 8 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 9 => some [(0,4),(0,5),(6,2),(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0),(2,4),(4,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 15 => some [(1,0),(5,5),(6,0),(7,0)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(0,1),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node1Domains1_fast_eq : root6Node1Domains1 = expandDomains root6Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node1Domains1 v = expandDomains root6Node1Domains1Fast v from by decide) v
theorem root6Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1_checked :
    checkReplacement table24 root6Node1Domains0 root6Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step1Chunk0_0_checked, root6Node1Step1Chunk0_1_checked, root6Node1Step1Chunk0_2_checked, root6Node1Step1Chunk0_3_checked, root6Node1Step1Chunk0_4_checked, root6Node1Step1Chunk0_5_checked, root6Node1Step1Chunk1_0_checked, root6Node1Step1Chunk1_1_checked, root6Node1Step1Chunk1_2_checked, root6Node1Step1Chunk1_3_checked, root6Node1Step1Chunk1_4_checked, root6Node1Step1Chunk1_5_checked, root6Node1Step1Chunk2_0_checked, root6Node1Step1Chunk2_1_checked, root6Node1Step1Chunk2_2_checked, root6Node1Step1Chunk2_3_checked, root6Node1Step1Chunk2_4_checked, root6Node1Step1Chunk2_5_checked, root6Node1Step1Chunk3_0_checked, root6Node1Step1Chunk3_1_checked, root6Node1Step1Chunk3_2_checked, root6Node1Step1Chunk3_3_checked, root6Node1Step1Chunk3_4_checked, root6Node1Step1Chunk3_5_checked, root6Node1Step1Chunk4_0_checked, root6Node1Step1Chunk4_1_checked, root6Node1Step1Chunk4_2_checked, root6Node1Step1Chunk4_3_checked, root6Node1Step1Chunk4_4_checked, root6Node1Step1Chunk4_5_checked, root6Node1Step1Chunk5_0_checked, root6Node1Step1Chunk5_1_checked, root6Node1Step1Chunk5_2_checked, root6Node1Step1Chunk5_3_checked, root6Node1Step1Chunk5_4_checked, root6Node1Step1Chunk5_5_checked, root6Node1Step1Chunk6_0_checked, root6Node1Step1Chunk6_1_checked, root6Node1Step1Chunk6_2_checked, root6Node1Step1Chunk6_3_checked, root6Node1Step1Chunk6_4_checked, root6Node1Step1Chunk6_5_checked, root6Node1Step1Chunk7_0_checked, root6Node1Step1Chunk7_1_checked, root6Node1Step1Chunk7_2_checked, root6Node1Step1Chunk7_3_checked, root6Node1Step1Chunk7_4_checked, root6Node1Step1Chunk7_5_checked, root6Node1Step1Chunk8_0_checked, root6Node1Step1Chunk8_1_checked, root6Node1Step1Chunk8_2_checked, root6Node1Step1Chunk8_3_checked, root6Node1Step1Chunk8_4_checked, root6Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node1Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5),(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5),(6,5)]
  | 4 => [(1,3),(5,2),(5,5)]
  | 5 => [(4,2)]
  | 6 => [(5,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(0,4),(0,5),(6,2),(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(1,0),(5,5),(6,0),(7,0)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => [(4,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(1,0),(4,2),(7,0),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root6Node1Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5),(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5),(6,5)]
  | 4 => some [(1,3),(5,2),(5,5)]
  | 5 => some [(4,2)]
  | 6 => some [(5,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,4),(0,5),(6,2),(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(1,0),(5,5),(6,0),(7,0)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 22 => some [(4,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(1,0),(4,2),(7,0),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node1Domains2_fast_eq : root6Node1Domains2 = expandDomains root6Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node1Domains2 v = expandDomains root6Node1Domains2Fast v from by decide) v
theorem root6Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2_checked :
    checkReplacement table12 root6Node1Domains1 root6Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step2Chunk0_0_checked, root6Node1Step2Chunk0_1_checked, root6Node1Step2Chunk0_2_checked, root6Node1Step2Chunk0_3_checked, root6Node1Step2Chunk0_4_checked, root6Node1Step2Chunk0_5_checked, root6Node1Step2Chunk1_0_checked, root6Node1Step2Chunk1_1_checked, root6Node1Step2Chunk1_2_checked, root6Node1Step2Chunk1_3_checked, root6Node1Step2Chunk1_4_checked, root6Node1Step2Chunk1_5_checked, root6Node1Step2Chunk2_0_checked, root6Node1Step2Chunk2_1_checked, root6Node1Step2Chunk2_2_checked, root6Node1Step2Chunk2_3_checked, root6Node1Step2Chunk2_4_checked, root6Node1Step2Chunk2_5_checked, root6Node1Step2Chunk3_0_checked, root6Node1Step2Chunk3_1_checked, root6Node1Step2Chunk3_2_checked, root6Node1Step2Chunk3_3_checked, root6Node1Step2Chunk3_4_checked, root6Node1Step2Chunk3_5_checked, root6Node1Step2Chunk4_0_checked, root6Node1Step2Chunk4_1_checked, root6Node1Step2Chunk4_2_checked, root6Node1Step2Chunk4_3_checked, root6Node1Step2Chunk4_4_checked, root6Node1Step2Chunk4_5_checked, root6Node1Step2Chunk5_0_checked, root6Node1Step2Chunk5_1_checked, root6Node1Step2Chunk5_2_checked, root6Node1Step2Chunk5_3_checked, root6Node1Step2Chunk5_4_checked, root6Node1Step2Chunk5_5_checked, root6Node1Step2Chunk6_0_checked, root6Node1Step2Chunk6_1_checked, root6Node1Step2Chunk6_2_checked, root6Node1Step2Chunk6_3_checked, root6Node1Step2Chunk6_4_checked, root6Node1Step2Chunk6_5_checked, root6Node1Step2Chunk7_0_checked, root6Node1Step2Chunk7_1_checked, root6Node1Step2Chunk7_2_checked, root6Node1Step2Chunk7_3_checked, root6Node1Step2Chunk7_4_checked, root6Node1Step2Chunk7_5_checked, root6Node1Step2Chunk8_0_checked, root6Node1Step2Chunk8_1_checked, root6Node1Step2Chunk8_2_checked, root6Node1Step2Chunk8_3_checked, root6Node1Step2Chunk8_4_checked, root6Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
