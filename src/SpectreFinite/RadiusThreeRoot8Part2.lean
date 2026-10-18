module

public import SpectreFinite.RadiusThreeRoot8Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable2
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node1Domains2 (v : Fin 37) : List State :=
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
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(4,2),(7,2),(8,2)]
  | _ => [(4,0),(5,0),(5,3),(8,0)]
def root8Node1Domains2Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(4,2),(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(5,3),(8,0)]
theorem root8Node1Domains2_fast_eq : root8Node1Domains2 = expandDomains root8Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node1Domains2 v = expandDomains root8Node1Domains2Fast v from by decide) v
theorem root8Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2_checked :
    checkReplacement table26 root8Node1Domains1 root8Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step2Chunk0_0_checked, root8Node1Step2Chunk0_1_checked, root8Node1Step2Chunk0_2_checked, root8Node1Step2Chunk0_3_checked, root8Node1Step2Chunk0_4_checked, root8Node1Step2Chunk0_5_checked, root8Node1Step2Chunk1_0_checked, root8Node1Step2Chunk1_1_checked, root8Node1Step2Chunk1_2_checked, root8Node1Step2Chunk1_3_checked, root8Node1Step2Chunk1_4_checked, root8Node1Step2Chunk1_5_checked, root8Node1Step2Chunk2_0_checked, root8Node1Step2Chunk2_1_checked, root8Node1Step2Chunk2_2_checked, root8Node1Step2Chunk2_3_checked, root8Node1Step2Chunk2_4_checked, root8Node1Step2Chunk2_5_checked, root8Node1Step2Chunk3_0_checked, root8Node1Step2Chunk3_1_checked, root8Node1Step2Chunk3_2_checked, root8Node1Step2Chunk3_3_checked, root8Node1Step2Chunk3_4_checked, root8Node1Step2Chunk3_5_checked, root8Node1Step2Chunk4_0_checked, root8Node1Step2Chunk4_1_checked, root8Node1Step2Chunk4_2_checked, root8Node1Step2Chunk4_3_checked, root8Node1Step2Chunk4_4_checked, root8Node1Step2Chunk4_5_checked, root8Node1Step2Chunk5_0_checked, root8Node1Step2Chunk5_1_checked, root8Node1Step2Chunk5_2_checked, root8Node1Step2Chunk5_3_checked, root8Node1Step2Chunk5_4_checked, root8Node1Step2Chunk5_5_checked, root8Node1Step2Chunk6_0_checked, root8Node1Step2Chunk6_1_checked, root8Node1Step2Chunk6_2_checked, root8Node1Step2Chunk6_3_checked, root8Node1Step2Chunk6_4_checked, root8Node1Step2Chunk6_5_checked, root8Node1Step2Chunk7_0_checked, root8Node1Step2Chunk7_1_checked, root8Node1Step2Chunk7_2_checked, root8Node1Step2Chunk7_3_checked, root8Node1Step2Chunk7_4_checked, root8Node1Step2Chunk7_5_checked, root8Node1Step2Chunk8_0_checked, root8Node1Step2Chunk8_1_checked, root8Node1Step2Chunk8_2_checked, root8Node1Step2Chunk8_3_checked, root8Node1Step2Chunk8_4_checked, root8Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node1Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0)]
  | 4 => [(1,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0),(7,4)]
  | 9 => [(0,3),(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(5,1),(8,1)]
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(1,4),(4,0),(7,4),(8,0)]
  | 34 => [(0,5),(1,3),(6,3),(7,3)]
  | 35 => [(4,2),(7,2),(8,2)]
  | _ => [(4,0),(5,0),(5,3),(8,0)]
def root8Node1Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(1,4),(4,0),(7,4),(8,0)]
  | 34 => some [(0,5),(1,3),(6,3),(7,3)]
  | 35 => some [(4,2),(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(5,3),(8,0)]
theorem root8Node1Domains3_fast_eq : root8Node1Domains3 = expandDomains root8Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node1Domains3 v = expandDomains root8Node1Domains3Fast v from by decide) v
theorem root8Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3_checked :
    checkReplacement table2 root8Node1Domains2 root8Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step3Chunk0_0_checked, root8Node1Step3Chunk0_1_checked, root8Node1Step3Chunk0_2_checked, root8Node1Step3Chunk0_3_checked, root8Node1Step3Chunk0_4_checked, root8Node1Step3Chunk0_5_checked, root8Node1Step3Chunk1_0_checked, root8Node1Step3Chunk1_1_checked, root8Node1Step3Chunk1_2_checked, root8Node1Step3Chunk1_3_checked, root8Node1Step3Chunk1_4_checked, root8Node1Step3Chunk1_5_checked, root8Node1Step3Chunk2_0_checked, root8Node1Step3Chunk2_1_checked, root8Node1Step3Chunk2_2_checked, root8Node1Step3Chunk2_3_checked, root8Node1Step3Chunk2_4_checked, root8Node1Step3Chunk2_5_checked, root8Node1Step3Chunk3_0_checked, root8Node1Step3Chunk3_1_checked, root8Node1Step3Chunk3_2_checked, root8Node1Step3Chunk3_3_checked, root8Node1Step3Chunk3_4_checked, root8Node1Step3Chunk3_5_checked, root8Node1Step3Chunk4_0_checked, root8Node1Step3Chunk4_1_checked, root8Node1Step3Chunk4_2_checked, root8Node1Step3Chunk4_3_checked, root8Node1Step3Chunk4_4_checked, root8Node1Step3Chunk4_5_checked, root8Node1Step3Chunk5_0_checked, root8Node1Step3Chunk5_1_checked, root8Node1Step3Chunk5_2_checked, root8Node1Step3Chunk5_3_checked, root8Node1Step3Chunk5_4_checked, root8Node1Step3Chunk5_5_checked, root8Node1Step3Chunk6_0_checked, root8Node1Step3Chunk6_1_checked, root8Node1Step3Chunk6_2_checked, root8Node1Step3Chunk6_3_checked, root8Node1Step3Chunk6_4_checked, root8Node1Step3Chunk6_5_checked, root8Node1Step3Chunk7_0_checked, root8Node1Step3Chunk7_1_checked, root8Node1Step3Chunk7_2_checked, root8Node1Step3Chunk7_3_checked, root8Node1Step3Chunk7_4_checked, root8Node1Step3Chunk7_5_checked, root8Node1Step3Chunk8_0_checked, root8Node1Step3Chunk8_1_checked, root8Node1Step3Chunk8_2_checked, root8Node1Step3Chunk8_3_checked, root8Node1Step3Chunk8_4_checked, root8Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node1Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0)]
  | 4 => [(1,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0),(7,4)]
  | 9 => [(0,3),(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1),(5,1),(8,1)]
  | 14 => [(0,1),(0,2),(6,5)]
  | 15 => [(2,0),(2,2),(2,4),(4,0)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(5,2),(5,5)]
  | 21 => [(1,0),(3,0),(5,0),(7,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(1,4),(6,4)]
  | 26 => [(0,5),(1,2)]
  | 27 => [(4,4),(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(4,0),(7,4),(8,0)]
  | 34 => [(1,3),(6,3),(7,3)]
  | 35 => [(4,2),(7,2),(8,2)]
  | _ => [(4,0),(5,0),(5,3),(8,0)]
def root8Node1Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(2,0),(2,2),(2,4),(4,0)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(7,4),(8,0)]
  | 34 => some [(1,3),(6,3),(7,3)]
  | 35 => some [(4,2),(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(5,3),(8,0)]
theorem root8Node1Domains4_fast_eq : root8Node1Domains4 = expandDomains root8Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node1Domains4 v = expandDomains root8Node1Domains4Fast v from by decide) v
theorem root8Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4_checked :
    checkReplacement table23 root8Node1Domains3 root8Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step4Chunk0_0_checked, root8Node1Step4Chunk0_1_checked, root8Node1Step4Chunk0_2_checked, root8Node1Step4Chunk0_3_checked, root8Node1Step4Chunk0_4_checked, root8Node1Step4Chunk0_5_checked, root8Node1Step4Chunk1_0_checked, root8Node1Step4Chunk1_1_checked, root8Node1Step4Chunk1_2_checked, root8Node1Step4Chunk1_3_checked, root8Node1Step4Chunk1_4_checked, root8Node1Step4Chunk1_5_checked, root8Node1Step4Chunk2_0_checked, root8Node1Step4Chunk2_1_checked, root8Node1Step4Chunk2_2_checked, root8Node1Step4Chunk2_3_checked, root8Node1Step4Chunk2_4_checked, root8Node1Step4Chunk2_5_checked, root8Node1Step4Chunk3_0_checked, root8Node1Step4Chunk3_1_checked, root8Node1Step4Chunk3_2_checked, root8Node1Step4Chunk3_3_checked, root8Node1Step4Chunk3_4_checked, root8Node1Step4Chunk3_5_checked, root8Node1Step4Chunk4_0_checked, root8Node1Step4Chunk4_1_checked, root8Node1Step4Chunk4_2_checked, root8Node1Step4Chunk4_3_checked, root8Node1Step4Chunk4_4_checked, root8Node1Step4Chunk4_5_checked, root8Node1Step4Chunk5_0_checked, root8Node1Step4Chunk5_1_checked, root8Node1Step4Chunk5_2_checked, root8Node1Step4Chunk5_3_checked, root8Node1Step4Chunk5_4_checked, root8Node1Step4Chunk5_5_checked, root8Node1Step4Chunk6_0_checked, root8Node1Step4Chunk6_1_checked, root8Node1Step4Chunk6_2_checked, root8Node1Step4Chunk6_3_checked, root8Node1Step4Chunk6_4_checked, root8Node1Step4Chunk6_5_checked, root8Node1Step4Chunk7_0_checked, root8Node1Step4Chunk7_1_checked, root8Node1Step4Chunk7_2_checked, root8Node1Step4Chunk7_3_checked, root8Node1Step4Chunk7_4_checked, root8Node1Step4Chunk7_5_checked, root8Node1Step4Chunk8_0_checked, root8Node1Step4Chunk8_1_checked, root8Node1Step4Chunk8_2_checked, root8Node1Step4Chunk8_3_checked, root8Node1Step4Chunk8_4_checked, root8Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
