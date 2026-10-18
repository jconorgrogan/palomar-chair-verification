module

public import SpectreFinite.RadiusThreeRoot8Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable0
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node0Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(4,2),(7,0),(8,0)]
  | 1 => [(4,3),(5,3),(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => [(1,0),(6,0),(7,0),(8,0)]
  | 4 => [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => [(0,1),(1,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => [(1,4),(4,0),(6,4),(7,4)]
  | 9 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(4,1),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(5,1),(7,5),(8,1)]
  | 14 => [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => stateChoices
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => stateChoices
  | _ => stateChoices
def root8Node0Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(4,2),(7,0),(8,0)]
  | 1 => some [(4,3),(5,3),(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0),(8,0)]
  | 4 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(4,0),(6,4),(7,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(5,1),(7,5),(8,1)]
  | 14 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => none
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => none
  | _ => none
theorem root8Node0Domains4_fast_eq : root8Node0Domains4 = expandDomains root8Node0Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node0Domains4 v = expandDomains root8Node0Domains4Fast v from by decide) v
theorem root8Node0Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root8Node0Domains3 root8Node0Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains3 root8Node0Domains4
    root8Node0Domains3Fast root8Node0Domains4Fast
    root8Node0Domains3_fast_eq root8Node0Domains4_fast_eq (by decide)
theorem root8Node0Step4_checked :
    checkReplacement table0 root8Node0Domains3 root8Node0Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node0Step4Chunk0_0_checked, root8Node0Step4Chunk0_1_checked, root8Node0Step4Chunk0_2_checked, root8Node0Step4Chunk0_3_checked, root8Node0Step4Chunk0_4_checked, root8Node0Step4Chunk0_5_checked, root8Node0Step4Chunk1_0_checked, root8Node0Step4Chunk1_1_checked, root8Node0Step4Chunk1_2_checked, root8Node0Step4Chunk1_3_checked, root8Node0Step4Chunk1_4_checked, root8Node0Step4Chunk1_5_checked, root8Node0Step4Chunk2_0_checked, root8Node0Step4Chunk2_1_checked, root8Node0Step4Chunk2_2_checked, root8Node0Step4Chunk2_3_checked, root8Node0Step4Chunk2_4_checked, root8Node0Step4Chunk2_5_checked, root8Node0Step4Chunk3_0_checked, root8Node0Step4Chunk3_1_checked, root8Node0Step4Chunk3_2_checked, root8Node0Step4Chunk3_3_checked, root8Node0Step4Chunk3_4_checked, root8Node0Step4Chunk3_5_checked, root8Node0Step4Chunk4_0_checked, root8Node0Step4Chunk4_1_checked, root8Node0Step4Chunk4_2_checked, root8Node0Step4Chunk4_3_checked, root8Node0Step4Chunk4_4_checked, root8Node0Step4Chunk4_5_checked, root8Node0Step4Chunk5_0_checked, root8Node0Step4Chunk5_1_checked, root8Node0Step4Chunk5_2_checked, root8Node0Step4Chunk5_3_checked, root8Node0Step4Chunk5_4_checked, root8Node0Step4Chunk5_5_checked, root8Node0Step4Chunk6_0_checked, root8Node0Step4Chunk6_1_checked, root8Node0Step4Chunk6_2_checked, root8Node0Step4Chunk6_3_checked, root8Node0Step4Chunk6_4_checked, root8Node0Step4Chunk6_5_checked, root8Node0Step4Chunk7_0_checked, root8Node0Step4Chunk7_1_checked, root8Node0Step4Chunk7_2_checked, root8Node0Step4Chunk7_3_checked, root8Node0Step4Chunk7_4_checked, root8Node0Step4Chunk7_5_checked, root8Node0Step4Chunk8_0_checked, root8Node0Step4Chunk8_1_checked, root8Node0Step4Chunk8_2_checked, root8Node0Step4Chunk8_3_checked, root8Node0Step4Chunk8_4_checked, root8Node0Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node0Domains5 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0),(4,2),(7,0),(8,0)]
  | 1 => [(4,3),(5,3),(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => [(1,0),(6,0),(7,0),(8,0)]
  | 4 => [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => [(0,1),(1,4),(7,4)]
  | 6 => [(0,5),(6,2),(6,3)]
  | 7 => [(4,4),(7,2),(8,4)]
  | 8 => [(1,4),(4,0),(6,4),(7,4)]
  | 9 => [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => [(4,1),(7,5),(8,5)]
  | 11 => [(0,2),(1,0),(6,0)]
  | 12 => [(1,1),(7,1)]
  | 13 => [(4,1),(5,1),(7,5),(8,1)]
  | 14 => [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(4,1),(7,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
def root8Node0Domains5Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(4,2),(7,0),(8,0)]
  | 1 => some [(4,3),(5,3),(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0),(8,0)]
  | 4 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(4,0),(6,4),(7,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1),(7,1)]
  | 13 => some [(4,1),(5,1),(7,5),(8,1)]
  | 14 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(4,1),(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => some [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
theorem root8Node0Domains5_fast_eq : root8Node0Domains5 = expandDomains root8Node0Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node0Domains5 v = expandDomains root8Node0Domains5Fast v from by decide) v
theorem root8Node0Step5Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node0Domains4 root8Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root8Node0Domains4 root8Node0Domains5
    root8Node0Domains4Fast root8Node0Domains5Fast
    root8Node0Domains4_fast_eq root8Node0Domains5_fast_eq (by decide)
theorem root8Node0Step5_checked :
    checkReplacement table25 root8Node0Domains4 root8Node0Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node0Step5Chunk0_0_checked, root8Node0Step5Chunk0_1_checked, root8Node0Step5Chunk0_2_checked, root8Node0Step5Chunk0_3_checked, root8Node0Step5Chunk0_4_checked, root8Node0Step5Chunk0_5_checked, root8Node0Step5Chunk1_0_checked, root8Node0Step5Chunk1_1_checked, root8Node0Step5Chunk1_2_checked, root8Node0Step5Chunk1_3_checked, root8Node0Step5Chunk1_4_checked, root8Node0Step5Chunk1_5_checked, root8Node0Step5Chunk2_0_checked, root8Node0Step5Chunk2_1_checked, root8Node0Step5Chunk2_2_checked, root8Node0Step5Chunk2_3_checked, root8Node0Step5Chunk2_4_checked, root8Node0Step5Chunk2_5_checked, root8Node0Step5Chunk3_0_checked, root8Node0Step5Chunk3_1_checked, root8Node0Step5Chunk3_2_checked, root8Node0Step5Chunk3_3_checked, root8Node0Step5Chunk3_4_checked, root8Node0Step5Chunk3_5_checked, root8Node0Step5Chunk4_0_checked, root8Node0Step5Chunk4_1_checked, root8Node0Step5Chunk4_2_checked, root8Node0Step5Chunk4_3_checked, root8Node0Step5Chunk4_4_checked, root8Node0Step5Chunk4_5_checked, root8Node0Step5Chunk5_0_checked, root8Node0Step5Chunk5_1_checked, root8Node0Step5Chunk5_2_checked, root8Node0Step5Chunk5_3_checked, root8Node0Step5Chunk5_4_checked, root8Node0Step5Chunk5_5_checked, root8Node0Step5Chunk6_0_checked, root8Node0Step5Chunk6_1_checked, root8Node0Step5Chunk6_2_checked, root8Node0Step5Chunk6_3_checked, root8Node0Step5Chunk6_4_checked, root8Node0Step5Chunk6_5_checked, root8Node0Step5Chunk7_0_checked, root8Node0Step5Chunk7_1_checked, root8Node0Step5Chunk7_2_checked, root8Node0Step5Chunk7_3_checked, root8Node0Step5Chunk7_4_checked, root8Node0Step5Chunk7_5_checked, root8Node0Step5Chunk8_0_checked, root8Node0Step5Chunk8_1_checked, root8Node0Step5Chunk8_2_checked, root8Node0Step5Chunk8_3_checked, root8Node0Step5Chunk8_4_checked, root8Node0Step5Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node1Domains0 : Domains 37 State := restrict root8Node0Domains5 12 (1,1)
def root8Node1Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(4,2),(7,0),(8,0)]
  | 1 => some [(4,3),(5,3),(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0),(8,0)]
  | 4 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 5 => some [(0,1),(1,4),(7,4)]
  | 6 => some [(0,5),(6,2),(6,3)]
  | 7 => some [(4,4),(7,2),(8,4)]
  | 8 => some [(1,4),(4,0),(6,4),(7,4)]
  | 9 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 10 => some [(4,1),(7,5),(8,5)]
  | 11 => some [(0,2),(1,0),(6,0)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(7,5),(8,1)]
  | 14 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(4,1),(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => some [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
theorem root8Node1Domains0_fast_eq : root8Node1Domains0 = expandDomains root8Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node1Domains0 v = expandDomains root8Node1Domains0Fast v from by decide) v
def root8Node1Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0),(8,0)]
  | 4 => [(1,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(1,4),(4,0),(6,4),(7,4)]
  | 9 => [(0,3),(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(5,1),(8,1)]
  | 14 => [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(7,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(4,1),(7,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
def root8Node1Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0),(8,0)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(1,4),(4,0),(6,4),(7,4)]
  | 9 => some [(0,3),(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(4,1),(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(2,2),(2,4),(4,2),(7,2),(8,2)]
  | _ => some [(1,3),(3,3),(4,0),(5,0),(5,3),(8,0)]
theorem root8Node1Domains1_fast_eq : root8Node1Domains1 = expandDomains root8Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node1Domains1 v = expandDomains root8Node1Domains1Fast v from by decide) v
theorem root8Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1_checked :
    checkReplacement table11 root8Node1Domains0 root8Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step1Chunk0_0_checked, root8Node1Step1Chunk0_1_checked, root8Node1Step1Chunk0_2_checked, root8Node1Step1Chunk0_3_checked, root8Node1Step1Chunk0_4_checked, root8Node1Step1Chunk0_5_checked, root8Node1Step1Chunk1_0_checked, root8Node1Step1Chunk1_1_checked, root8Node1Step1Chunk1_2_checked, root8Node1Step1Chunk1_3_checked, root8Node1Step1Chunk1_4_checked, root8Node1Step1Chunk1_5_checked, root8Node1Step1Chunk2_0_checked, root8Node1Step1Chunk2_1_checked, root8Node1Step1Chunk2_2_checked, root8Node1Step1Chunk2_3_checked, root8Node1Step1Chunk2_4_checked, root8Node1Step1Chunk2_5_checked, root8Node1Step1Chunk3_0_checked, root8Node1Step1Chunk3_1_checked, root8Node1Step1Chunk3_2_checked, root8Node1Step1Chunk3_3_checked, root8Node1Step1Chunk3_4_checked, root8Node1Step1Chunk3_5_checked, root8Node1Step1Chunk4_0_checked, root8Node1Step1Chunk4_1_checked, root8Node1Step1Chunk4_2_checked, root8Node1Step1Chunk4_3_checked, root8Node1Step1Chunk4_4_checked, root8Node1Step1Chunk4_5_checked, root8Node1Step1Chunk5_0_checked, root8Node1Step1Chunk5_1_checked, root8Node1Step1Chunk5_2_checked, root8Node1Step1Chunk5_3_checked, root8Node1Step1Chunk5_4_checked, root8Node1Step1Chunk5_5_checked, root8Node1Step1Chunk6_0_checked, root8Node1Step1Chunk6_1_checked, root8Node1Step1Chunk6_2_checked, root8Node1Step1Chunk6_3_checked, root8Node1Step1Chunk6_4_checked, root8Node1Step1Chunk6_5_checked, root8Node1Step1Chunk7_0_checked, root8Node1Step1Chunk7_1_checked, root8Node1Step1Chunk7_2_checked, root8Node1Step1Chunk7_3_checked, root8Node1Step1Chunk7_4_checked, root8Node1Step1Chunk7_5_checked, root8Node1Step1Chunk8_0_checked, root8Node1Step1Chunk8_1_checked, root8Node1Step1Chunk8_2_checked, root8Node1Step1Chunk8_3_checked, root8Node1Step1Chunk8_4_checked, root8Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
