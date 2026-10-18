module

public import SpectreFinite.RadiusThreeRoot1Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable10
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable17

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node1Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(7,5)]
  | 1 => [(0,3),(1,1),(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5),(1,2),(3,2),(6,3)]
  | 5 => [(2,0),(2,2),(4,0)]
  | 6 => [(3,3),(7,3)]
  | 7 => [(5,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(0,2),(0,3),(6,0),(6,1)]
  | 10 => [(1,1),(3,1),(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(4,2),(5,2),(7,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => [(7,4),(8,4)]
  | 23 => [(0,0),(1,3),(6,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,0),(4,2),(7,0),(8,2)]
  | 28 => [(0,2),(1,5),(6,5)]
  | 29 => [(0,4),(1,1),(6,1)]
  | 30 => [(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,4)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root1Node1Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5),(1,2),(3,2),(6,3)]
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3),(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,2),(0,3),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => some [(7,4),(8,4)]
  | 23 => some [(0,0),(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root1Node1Domains3_fast_eq : root1Node1Domains3 = expandDomains root1Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node1Domains3 v = expandDomains root1Node1Domains3Fast v from by decide) v
theorem root1Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3_checked :
    checkReplacement table10 root1Node1Domains2 root1Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node1Step3Chunk0_0_checked, root1Node1Step3Chunk0_1_checked, root1Node1Step3Chunk0_2_checked, root1Node1Step3Chunk0_3_checked, root1Node1Step3Chunk0_4_checked, root1Node1Step3Chunk0_5_checked, root1Node1Step3Chunk1_0_checked, root1Node1Step3Chunk1_1_checked, root1Node1Step3Chunk1_2_checked, root1Node1Step3Chunk1_3_checked, root1Node1Step3Chunk1_4_checked, root1Node1Step3Chunk1_5_checked, root1Node1Step3Chunk2_0_checked, root1Node1Step3Chunk2_1_checked, root1Node1Step3Chunk2_2_checked, root1Node1Step3Chunk2_3_checked, root1Node1Step3Chunk2_4_checked, root1Node1Step3Chunk2_5_checked, root1Node1Step3Chunk3_0_checked, root1Node1Step3Chunk3_1_checked, root1Node1Step3Chunk3_2_checked, root1Node1Step3Chunk3_3_checked, root1Node1Step3Chunk3_4_checked, root1Node1Step3Chunk3_5_checked, root1Node1Step3Chunk4_0_checked, root1Node1Step3Chunk4_1_checked, root1Node1Step3Chunk4_2_checked, root1Node1Step3Chunk4_3_checked, root1Node1Step3Chunk4_4_checked, root1Node1Step3Chunk4_5_checked, root1Node1Step3Chunk5_0_checked, root1Node1Step3Chunk5_1_checked, root1Node1Step3Chunk5_2_checked, root1Node1Step3Chunk5_3_checked, root1Node1Step3Chunk5_4_checked, root1Node1Step3Chunk5_5_checked, root1Node1Step3Chunk6_0_checked, root1Node1Step3Chunk6_1_checked, root1Node1Step3Chunk6_2_checked, root1Node1Step3Chunk6_3_checked, root1Node1Step3Chunk6_4_checked, root1Node1Step3Chunk6_5_checked, root1Node1Step3Chunk7_0_checked, root1Node1Step3Chunk7_1_checked, root1Node1Step3Chunk7_2_checked, root1Node1Step3Chunk7_3_checked, root1Node1Step3Chunk7_4_checked, root1Node1Step3Chunk7_5_checked, root1Node1Step3Chunk8_0_checked, root1Node1Step3Chunk8_1_checked, root1Node1Step3Chunk8_2_checked, root1Node1Step3Chunk8_3_checked, root1Node1Step3Chunk8_4_checked, root1Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node1Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(7,5)]
  | 1 => [(0,3),(1,1),(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5),(1,2),(3,2),(6,3)]
  | 5 => [(2,0),(2,2),(4,0)]
  | 6 => [(3,3),(7,3)]
  | 7 => [(5,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(0,2),(0,3),(6,0),(6,1)]
  | 10 => [(1,1),(3,1),(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(4,2),(5,2),(7,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(7,4),(8,4)]
  | 23 => [(0,0),(1,3),(6,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(0,2),(1,5),(6,5)]
  | 29 => [(0,4),(1,1),(6,1)]
  | 30 => [(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,4)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root1Node1Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5),(1,2),(3,2),(6,3)]
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3),(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,2),(0,3),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(7,4),(8,4)]
  | 23 => some [(0,0),(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root1Node1Domains4_fast_eq : root1Node1Domains4 = expandDomains root1Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node1Domains4 v = expandDomains root1Node1Domains4Fast v from by decide) v
theorem root1Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4_checked :
    checkReplacement table13 root1Node1Domains3 root1Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node1Step4Chunk0_0_checked, root1Node1Step4Chunk0_1_checked, root1Node1Step4Chunk0_2_checked, root1Node1Step4Chunk0_3_checked, root1Node1Step4Chunk0_4_checked, root1Node1Step4Chunk0_5_checked, root1Node1Step4Chunk1_0_checked, root1Node1Step4Chunk1_1_checked, root1Node1Step4Chunk1_2_checked, root1Node1Step4Chunk1_3_checked, root1Node1Step4Chunk1_4_checked, root1Node1Step4Chunk1_5_checked, root1Node1Step4Chunk2_0_checked, root1Node1Step4Chunk2_1_checked, root1Node1Step4Chunk2_2_checked, root1Node1Step4Chunk2_3_checked, root1Node1Step4Chunk2_4_checked, root1Node1Step4Chunk2_5_checked, root1Node1Step4Chunk3_0_checked, root1Node1Step4Chunk3_1_checked, root1Node1Step4Chunk3_2_checked, root1Node1Step4Chunk3_3_checked, root1Node1Step4Chunk3_4_checked, root1Node1Step4Chunk3_5_checked, root1Node1Step4Chunk4_0_checked, root1Node1Step4Chunk4_1_checked, root1Node1Step4Chunk4_2_checked, root1Node1Step4Chunk4_3_checked, root1Node1Step4Chunk4_4_checked, root1Node1Step4Chunk4_5_checked, root1Node1Step4Chunk5_0_checked, root1Node1Step4Chunk5_1_checked, root1Node1Step4Chunk5_2_checked, root1Node1Step4Chunk5_3_checked, root1Node1Step4Chunk5_4_checked, root1Node1Step4Chunk5_5_checked, root1Node1Step4Chunk6_0_checked, root1Node1Step4Chunk6_1_checked, root1Node1Step4Chunk6_2_checked, root1Node1Step4Chunk6_3_checked, root1Node1Step4Chunk6_4_checked, root1Node1Step4Chunk6_5_checked, root1Node1Step4Chunk7_0_checked, root1Node1Step4Chunk7_1_checked, root1Node1Step4Chunk7_2_checked, root1Node1Step4Chunk7_3_checked, root1Node1Step4Chunk7_4_checked, root1Node1Step4Chunk7_5_checked, root1Node1Step4Chunk8_0_checked, root1Node1Step4Chunk8_1_checked, root1Node1Step4Chunk8_2_checked, root1Node1Step4Chunk8_3_checked, root1Node1Step4Chunk8_4_checked, root1Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node2Domains0 : Domains 37 State := restrict root1Node1Domains4 6 (3,3)
def root1Node2Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5),(1,2),(3,2),(6,3)]
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,2),(0,3),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(7,4),(8,4)]
  | 23 => some [(0,0),(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root1Node2Domains0_fast_eq : root1Node2Domains0 = expandDomains root1Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node2Domains0 v = expandDomains root1Node2Domains0Fast v from by decide) v
def root1Node2Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(7,5)]
  | 1 => [(0,3),(1,1),(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(6,3)]
  | 5 => [(2,2)]
  | 6 => [(3,3)]
  | 7 => [(5,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,0),(0,1),(6,4)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root1Node2Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(6,3)]
  | 5 => some [(2,2)]
  | 6 => some [(3,3)]
  | 7 => some [(5,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root1Node2Domains1_fast_eq : root1Node2Domains1 = expandDomains root1Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node2Domains1 v = expandDomains root1Node2Domains1Fast v from by decide) v
theorem root1Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1_checked :
    checkReplacement table17 root1Node2Domains0 root1Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node2Step1Chunk0_0_checked, root1Node2Step1Chunk0_1_checked, root1Node2Step1Chunk0_2_checked, root1Node2Step1Chunk0_3_checked, root1Node2Step1Chunk0_4_checked, root1Node2Step1Chunk0_5_checked, root1Node2Step1Chunk1_0_checked, root1Node2Step1Chunk1_1_checked, root1Node2Step1Chunk1_2_checked, root1Node2Step1Chunk1_3_checked, root1Node2Step1Chunk1_4_checked, root1Node2Step1Chunk1_5_checked, root1Node2Step1Chunk2_0_checked, root1Node2Step1Chunk2_1_checked, root1Node2Step1Chunk2_2_checked, root1Node2Step1Chunk2_3_checked, root1Node2Step1Chunk2_4_checked, root1Node2Step1Chunk2_5_checked, root1Node2Step1Chunk3_0_checked, root1Node2Step1Chunk3_1_checked, root1Node2Step1Chunk3_2_checked, root1Node2Step1Chunk3_3_checked, root1Node2Step1Chunk3_4_checked, root1Node2Step1Chunk3_5_checked, root1Node2Step1Chunk4_0_checked, root1Node2Step1Chunk4_1_checked, root1Node2Step1Chunk4_2_checked, root1Node2Step1Chunk4_3_checked, root1Node2Step1Chunk4_4_checked, root1Node2Step1Chunk4_5_checked, root1Node2Step1Chunk5_0_checked, root1Node2Step1Chunk5_1_checked, root1Node2Step1Chunk5_2_checked, root1Node2Step1Chunk5_3_checked, root1Node2Step1Chunk5_4_checked, root1Node2Step1Chunk5_5_checked, root1Node2Step1Chunk6_0_checked, root1Node2Step1Chunk6_1_checked, root1Node2Step1Chunk6_2_checked, root1Node2Step1Chunk6_3_checked, root1Node2Step1Chunk6_4_checked, root1Node2Step1Chunk6_5_checked, root1Node2Step1Chunk7_0_checked, root1Node2Step1Chunk7_1_checked, root1Node2Step1Chunk7_2_checked, root1Node2Step1Chunk7_3_checked, root1Node2Step1Chunk7_4_checked, root1Node2Step1Chunk7_5_checked, root1Node2Step1Chunk8_0_checked, root1Node2Step1Chunk8_1_checked, root1Node2Step1Chunk8_2_checked, root1Node2Step1Chunk8_3_checked, root1Node2Step1Chunk8_4_checked, root1Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
