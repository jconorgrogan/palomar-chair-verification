module

public import SpectreFinite.RadiusThreeRoot0Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable24
public import SpectreFinite.RadiusThreeTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node0Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(4,0),(7,4)]
  | 1 => [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,4),(8,4)]
  | 3 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 4 => [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 8 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 9 => [(1,3),(7,3),(8,3)]
  | 10 => [(5,2),(5,5),(8,2)]
  | 11 => [(1,0),(3,0),(5,0)]
  | 12 => [(2,1),(2,5),(4,5)]
  | 13 => [(0,2),(1,0),(6,0),(7,0)]
  | 14 => [(1,1),(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(1,4),(6,4),(6,5)]
  | 16 => [(0,4),(0,5),(1,2),(6,2)]
  | 17 => [(4,4),(5,4),(8,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2),(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0),(6,0),(7,0)]
  | 23 => [(4,3),(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(1,4),(5,0),(5,3)]
  | 29 => [(0,5),(4,5),(5,5),(8,5)]
  | 30 => [(2,0),(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,0),(6,3)]
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node0Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(4,0),(7,4)]
  | 1 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 4 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 8 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 9 => some [(1,3),(7,3),(8,3)]
  | 10 => some [(5,2),(5,5),(8,2)]
  | 11 => some [(1,0),(3,0),(5,0)]
  | 12 => some [(2,1),(2,5),(4,5)]
  | 13 => some [(0,2),(1,0),(6,0),(7,0)]
  | 14 => some [(1,1),(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,4),(0,5),(1,2),(6,2)]
  | 17 => some [(4,4),(5,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2),(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0),(6,0),(7,0)]
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(1,4),(5,0),(5,3)]
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,0),(6,3)]
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node0Domains4_fast_eq : root0Node0Domains4 = expandDomains root0Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node0Domains4 v = expandDomains root0Node0Domains4Fast v from by decide) v
theorem root0Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root0Node0Domains3 root0Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains3 root0Node0Domains4
    root0Node0Domains3Fast root0Node0Domains4Fast
    root0Node0Domains3_fast_eq root0Node0Domains4_fast_eq (by decide)
theorem root0Node0Step4_checked :
    checkReplacement table22 root0Node0Domains3 root0Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node0Step4Chunk0_0_checked, root0Node0Step4Chunk0_1_checked, root0Node0Step4Chunk0_2_checked, root0Node0Step4Chunk0_3_checked, root0Node0Step4Chunk0_4_checked, root0Node0Step4Chunk0_5_checked, root0Node0Step4Chunk1_0_checked, root0Node0Step4Chunk1_1_checked, root0Node0Step4Chunk1_2_checked, root0Node0Step4Chunk1_3_checked, root0Node0Step4Chunk1_4_checked, root0Node0Step4Chunk1_5_checked, root0Node0Step4Chunk2_0_checked, root0Node0Step4Chunk2_1_checked, root0Node0Step4Chunk2_2_checked, root0Node0Step4Chunk2_3_checked, root0Node0Step4Chunk2_4_checked, root0Node0Step4Chunk2_5_checked, root0Node0Step4Chunk3_0_checked, root0Node0Step4Chunk3_1_checked, root0Node0Step4Chunk3_2_checked, root0Node0Step4Chunk3_3_checked, root0Node0Step4Chunk3_4_checked, root0Node0Step4Chunk3_5_checked, root0Node0Step4Chunk4_0_checked, root0Node0Step4Chunk4_1_checked, root0Node0Step4Chunk4_2_checked, root0Node0Step4Chunk4_3_checked, root0Node0Step4Chunk4_4_checked, root0Node0Step4Chunk4_5_checked, root0Node0Step4Chunk5_0_checked, root0Node0Step4Chunk5_1_checked, root0Node0Step4Chunk5_2_checked, root0Node0Step4Chunk5_3_checked, root0Node0Step4Chunk5_4_checked, root0Node0Step4Chunk5_5_checked, root0Node0Step4Chunk6_0_checked, root0Node0Step4Chunk6_1_checked, root0Node0Step4Chunk6_2_checked, root0Node0Step4Chunk6_3_checked, root0Node0Step4Chunk6_4_checked, root0Node0Step4Chunk6_5_checked, root0Node0Step4Chunk7_0_checked, root0Node0Step4Chunk7_1_checked, root0Node0Step4Chunk7_2_checked, root0Node0Step4Chunk7_3_checked, root0Node0Step4Chunk7_4_checked, root0Node0Step4Chunk7_5_checked, root0Node0Step4Chunk8_0_checked, root0Node0Step4Chunk8_1_checked, root0Node0Step4Chunk8_2_checked, root0Node0Step4Chunk8_3_checked, root0Node0Step4Chunk8_4_checked, root0Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node1Domains0 : Domains 37 State := restrict root0Node0Domains4 19 (3,2)
def root0Node1Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(4,0),(7,4)]
  | 1 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,4),(8,4)]
  | 3 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 4 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 5 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 6 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 7 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 8 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 9 => some [(1,3),(7,3),(8,3)]
  | 10 => some [(5,2),(5,5),(8,2)]
  | 11 => some [(1,0),(3,0),(5,0)]
  | 12 => some [(2,1),(2,5),(4,5)]
  | 13 => some [(0,2),(1,0),(6,0),(7,0)]
  | 14 => some [(1,1),(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,4),(0,5),(1,2),(6,2)]
  | 17 => some [(4,4),(5,4),(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0),(6,0),(7,0)]
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(1,4),(5,0),(5,3)]
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,0),(6,3)]
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node1Domains0_fast_eq : root0Node1Domains0 = expandDomains root0Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node1Domains0 v = expandDomains root0Node1Domains0Fast v from by decide) v
def root0Node1Domains1 (v : Fin 37) : List State :=
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
  | 14 => [(1,1),(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(1,4),(6,4),(6,5)]
  | 16 => [(0,4),(0,5),(1,2),(6,2)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0),(6,0),(7,0)]
  | 23 => [(4,3),(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(1,4),(5,0),(5,3)]
  | 29 => [(0,5),(4,5),(5,5),(8,5)]
  | 30 => [(2,0),(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,0),(6,3)]
  | 34 => [(3,1),(4,4),(7,2)]
  | 35 => [(0,1),(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node1Domains1Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(1,1),(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,4),(0,5),(1,2),(6,2)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0),(6,0),(7,0)]
  | 23 => some [(4,3),(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(1,4),(5,0),(5,3)]
  | 29 => some [(0,5),(4,5),(5,5),(8,5)]
  | 30 => some [(2,0),(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,0),(6,3)]
  | 34 => some [(3,1),(4,4),(7,2)]
  | 35 => some [(0,1),(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node1Domains1_fast_eq : root0Node1Domains1 = expandDomains root0Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node1Domains1 v = expandDomains root0Node1Domains1Fast v from by decide) v
theorem root0Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1_checked :
    checkReplacement table6 root0Node1Domains0 root0Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step1Chunk0_0_checked, root0Node1Step1Chunk0_1_checked, root0Node1Step1Chunk0_2_checked, root0Node1Step1Chunk0_3_checked, root0Node1Step1Chunk0_4_checked, root0Node1Step1Chunk0_5_checked, root0Node1Step1Chunk1_0_checked, root0Node1Step1Chunk1_1_checked, root0Node1Step1Chunk1_2_checked, root0Node1Step1Chunk1_3_checked, root0Node1Step1Chunk1_4_checked, root0Node1Step1Chunk1_5_checked, root0Node1Step1Chunk2_0_checked, root0Node1Step1Chunk2_1_checked, root0Node1Step1Chunk2_2_checked, root0Node1Step1Chunk2_3_checked, root0Node1Step1Chunk2_4_checked, root0Node1Step1Chunk2_5_checked, root0Node1Step1Chunk3_0_checked, root0Node1Step1Chunk3_1_checked, root0Node1Step1Chunk3_2_checked, root0Node1Step1Chunk3_3_checked, root0Node1Step1Chunk3_4_checked, root0Node1Step1Chunk3_5_checked, root0Node1Step1Chunk4_0_checked, root0Node1Step1Chunk4_1_checked, root0Node1Step1Chunk4_2_checked, root0Node1Step1Chunk4_3_checked, root0Node1Step1Chunk4_4_checked, root0Node1Step1Chunk4_5_checked, root0Node1Step1Chunk5_0_checked, root0Node1Step1Chunk5_1_checked, root0Node1Step1Chunk5_2_checked, root0Node1Step1Chunk5_3_checked, root0Node1Step1Chunk5_4_checked, root0Node1Step1Chunk5_5_checked, root0Node1Step1Chunk6_0_checked, root0Node1Step1Chunk6_1_checked, root0Node1Step1Chunk6_2_checked, root0Node1Step1Chunk6_3_checked, root0Node1Step1Chunk6_4_checked, root0Node1Step1Chunk6_5_checked, root0Node1Step1Chunk7_0_checked, root0Node1Step1Chunk7_1_checked, root0Node1Step1Chunk7_2_checked, root0Node1Step1Chunk7_3_checked, root0Node1Step1Chunk7_4_checked, root0Node1Step1Chunk7_5_checked, root0Node1Step1Chunk8_0_checked, root0Node1Step1Chunk8_1_checked, root0Node1Step1Chunk8_2_checked, root0Node1Step1Chunk8_3_checked, root0Node1Step1Chunk8_4_checked, root0Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node1Domains2 (v : Fin 37) : List State :=
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
  | 14 => [(1,1),(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(1,4),(6,4),(6,5)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(6,0)]
  | 23 => [(7,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(5,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0)]
  | 34 => [(7,2)]
  | 35 => [(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,2),(6,3)]
def root0Node1Domains2Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(1,1),(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(1,4),(6,4),(6,5)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(6,0)]
  | 23 => some [(7,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0)]
  | 34 => some [(7,2)]
  | 35 => some [(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,2),(6,3)]
theorem root0Node1Domains2_fast_eq : root0Node1Domains2 = expandDomains root0Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node1Domains2 v = expandDomains root0Node1Domains2Fast v from by decide) v
theorem root0Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2_checked :
    checkReplacement table24 root0Node1Domains1 root0Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step2Chunk0_0_checked, root0Node1Step2Chunk0_1_checked, root0Node1Step2Chunk0_2_checked, root0Node1Step2Chunk0_3_checked, root0Node1Step2Chunk0_4_checked, root0Node1Step2Chunk0_5_checked, root0Node1Step2Chunk1_0_checked, root0Node1Step2Chunk1_1_checked, root0Node1Step2Chunk1_2_checked, root0Node1Step2Chunk1_3_checked, root0Node1Step2Chunk1_4_checked, root0Node1Step2Chunk1_5_checked, root0Node1Step2Chunk2_0_checked, root0Node1Step2Chunk2_1_checked, root0Node1Step2Chunk2_2_checked, root0Node1Step2Chunk2_3_checked, root0Node1Step2Chunk2_4_checked, root0Node1Step2Chunk2_5_checked, root0Node1Step2Chunk3_0_checked, root0Node1Step2Chunk3_1_checked, root0Node1Step2Chunk3_2_checked, root0Node1Step2Chunk3_3_checked, root0Node1Step2Chunk3_4_checked, root0Node1Step2Chunk3_5_checked, root0Node1Step2Chunk4_0_checked, root0Node1Step2Chunk4_1_checked, root0Node1Step2Chunk4_2_checked, root0Node1Step2Chunk4_3_checked, root0Node1Step2Chunk4_4_checked, root0Node1Step2Chunk4_5_checked, root0Node1Step2Chunk5_0_checked, root0Node1Step2Chunk5_1_checked, root0Node1Step2Chunk5_2_checked, root0Node1Step2Chunk5_3_checked, root0Node1Step2Chunk5_4_checked, root0Node1Step2Chunk5_5_checked, root0Node1Step2Chunk6_0_checked, root0Node1Step2Chunk6_1_checked, root0Node1Step2Chunk6_2_checked, root0Node1Step2Chunk6_3_checked, root0Node1Step2Chunk6_4_checked, root0Node1Step2Chunk6_5_checked, root0Node1Step2Chunk7_0_checked, root0Node1Step2Chunk7_1_checked, root0Node1Step2Chunk7_2_checked, root0Node1Step2Chunk7_3_checked, root0Node1Step2Chunk7_4_checked, root0Node1Step2Chunk7_5_checked, root0Node1Step2Chunk8_0_checked, root0Node1Step2Chunk8_1_checked, root0Node1Step2Chunk8_2_checked, root0Node1Step2Chunk8_3_checked, root0Node1Step2Chunk8_4_checked, root0Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
