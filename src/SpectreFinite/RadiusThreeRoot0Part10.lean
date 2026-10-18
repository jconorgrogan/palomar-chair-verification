module

public import SpectreFinite.RadiusThreeRoot0Part9
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node14Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,4),(7,4)]
  | 1 => [(0,5),(6,3)]
  | 2 => [(2,0),(2,2),(2,4),(4,4)]
  | 3 => [(0,0),(1,3),(3,3),(7,3)]
  | 4 => [(4,1),(7,5)]
  | 5 => [(0,2),(6,0)]
  | 6 => [(1,1),(3,1),(7,1)]
  | 7 => [(0,1),(1,5),(6,5)]
  | 8 => [(0,4),(6,1),(6,2)]
  | 9 => [(7,3)]
  | 10 => [(5,2),(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(6,4)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0)]
  | 23 => [(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,3)]
  | 34 => [(4,4),(7,2)]
  | 35 => [(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,3)]
def root0Node14Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4),(7,4)]
  | 1 => some [(0,5),(6,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,4)]
  | 3 => some [(0,0),(1,3),(3,3),(7,3)]
  | 4 => some [(4,1),(7,5)]
  | 5 => some [(0,2),(6,0)]
  | 6 => some [(1,1),(3,1),(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2),(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node14Domains3_fast_eq : root0Node14Domains3 = expandDomains root0Node14Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node14Domains3 v = expandDomains root0Node14Domains3Fast v from by decide) v
theorem root0Node14Step3Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root0Node14Domains2 root0Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains2 root0Node14Domains3
    root0Node14Domains2Fast root0Node14Domains3Fast
    root0Node14Domains2_fast_eq root0Node14Domains3_fast_eq (by decide)
theorem root0Node14Step3_checked :
    checkReplacement table30 root0Node14Domains2 root0Node14Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node14Step3Chunk0_0_checked, root0Node14Step3Chunk0_1_checked, root0Node14Step3Chunk0_2_checked, root0Node14Step3Chunk0_3_checked, root0Node14Step3Chunk0_4_checked, root0Node14Step3Chunk0_5_checked, root0Node14Step3Chunk1_0_checked, root0Node14Step3Chunk1_1_checked, root0Node14Step3Chunk1_2_checked, root0Node14Step3Chunk1_3_checked, root0Node14Step3Chunk1_4_checked, root0Node14Step3Chunk1_5_checked, root0Node14Step3Chunk2_0_checked, root0Node14Step3Chunk2_1_checked, root0Node14Step3Chunk2_2_checked, root0Node14Step3Chunk2_3_checked, root0Node14Step3Chunk2_4_checked, root0Node14Step3Chunk2_5_checked, root0Node14Step3Chunk3_0_checked, root0Node14Step3Chunk3_1_checked, root0Node14Step3Chunk3_2_checked, root0Node14Step3Chunk3_3_checked, root0Node14Step3Chunk3_4_checked, root0Node14Step3Chunk3_5_checked, root0Node14Step3Chunk4_0_checked, root0Node14Step3Chunk4_1_checked, root0Node14Step3Chunk4_2_checked, root0Node14Step3Chunk4_3_checked, root0Node14Step3Chunk4_4_checked, root0Node14Step3Chunk4_5_checked, root0Node14Step3Chunk5_0_checked, root0Node14Step3Chunk5_1_checked, root0Node14Step3Chunk5_2_checked, root0Node14Step3Chunk5_3_checked, root0Node14Step3Chunk5_4_checked, root0Node14Step3Chunk5_5_checked, root0Node14Step3Chunk6_0_checked, root0Node14Step3Chunk6_1_checked, root0Node14Step3Chunk6_2_checked, root0Node14Step3Chunk6_3_checked, root0Node14Step3Chunk6_4_checked, root0Node14Step3Chunk6_5_checked, root0Node14Step3Chunk7_0_checked, root0Node14Step3Chunk7_1_checked, root0Node14Step3Chunk7_2_checked, root0Node14Step3Chunk7_3_checked, root0Node14Step3Chunk7_4_checked, root0Node14Step3Chunk7_5_checked, root0Node14Step3Chunk8_0_checked, root0Node14Step3Chunk8_1_checked, root0Node14Step3Chunk8_2_checked, root0Node14Step3Chunk8_3_checked, root0Node14Step3Chunk8_4_checked, root0Node14Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node15Domains0 : Domains 37 State := restrict root0Node14Domains3 0 (1,4)
def root0Node15Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5),(6,3)]
  | 2 => some [(2,0),(2,2),(2,4),(4,4)]
  | 3 => some [(0,0),(1,3),(3,3),(7,3)]
  | 4 => some [(4,1),(7,5)]
  | 5 => some [(0,2),(6,0)]
  | 6 => some [(1,1),(3,1),(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(5,2),(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node15Domains0_fast_eq : root0Node15Domains0 = expandDomains root0Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node15Domains0 v = expandDomains root0Node15Domains0Fast v from by decide) v
def root0Node15Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0),(2,4),(4,4)]
  | 3 => [(0,0),(1,3),(7,3)]
  | 4 => [(7,5)]
  | 5 => [(6,0)]
  | 6 => [(3,1),(7,1)]
  | 7 => [(0,1),(1,5),(6,5)]
  | 8 => [(0,4),(6,1),(6,2)]
  | 9 => [(7,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(4,3),(7,1),(8,3)]
  | 15 => [(0,1),(6,4)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0),(7,4)]
  | 21 => [(1,3),(6,3),(7,3)]
  | 22 => [(0,3),(1,0)]
  | 23 => [(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(5,1),(8,1)]
  | 27 => [(0,1),(0,2),(6,5)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,3)]
  | 34 => [(4,4),(7,2)]
  | 35 => [(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,3)]
def root0Node15Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,0),(2,4),(4,4)]
  | 3 => some [(0,0),(1,3),(7,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(3,1),(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node15Domains1_fast_eq : root0Node15Domains1 = expandDomains root0Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node15Domains1 v = expandDomains root0Node15Domains1Fast v from by decide) v
theorem root0Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1_checked :
    checkReplacement table1 root0Node15Domains0 root0Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node15Step1Chunk0_0_checked, root0Node15Step1Chunk0_1_checked, root0Node15Step1Chunk0_2_checked, root0Node15Step1Chunk0_3_checked, root0Node15Step1Chunk0_4_checked, root0Node15Step1Chunk0_5_checked, root0Node15Step1Chunk1_0_checked, root0Node15Step1Chunk1_1_checked, root0Node15Step1Chunk1_2_checked, root0Node15Step1Chunk1_3_checked, root0Node15Step1Chunk1_4_checked, root0Node15Step1Chunk1_5_checked, root0Node15Step1Chunk2_0_checked, root0Node15Step1Chunk2_1_checked, root0Node15Step1Chunk2_2_checked, root0Node15Step1Chunk2_3_checked, root0Node15Step1Chunk2_4_checked, root0Node15Step1Chunk2_5_checked, root0Node15Step1Chunk3_0_checked, root0Node15Step1Chunk3_1_checked, root0Node15Step1Chunk3_2_checked, root0Node15Step1Chunk3_3_checked, root0Node15Step1Chunk3_4_checked, root0Node15Step1Chunk3_5_checked, root0Node15Step1Chunk4_0_checked, root0Node15Step1Chunk4_1_checked, root0Node15Step1Chunk4_2_checked, root0Node15Step1Chunk4_3_checked, root0Node15Step1Chunk4_4_checked, root0Node15Step1Chunk4_5_checked, root0Node15Step1Chunk5_0_checked, root0Node15Step1Chunk5_1_checked, root0Node15Step1Chunk5_2_checked, root0Node15Step1Chunk5_3_checked, root0Node15Step1Chunk5_4_checked, root0Node15Step1Chunk5_5_checked, root0Node15Step1Chunk6_0_checked, root0Node15Step1Chunk6_1_checked, root0Node15Step1Chunk6_2_checked, root0Node15Step1Chunk6_3_checked, root0Node15Step1Chunk6_4_checked, root0Node15Step1Chunk6_5_checked, root0Node15Step1Chunk7_0_checked, root0Node15Step1Chunk7_1_checked, root0Node15Step1Chunk7_2_checked, root0Node15Step1Chunk7_3_checked, root0Node15Step1Chunk7_4_checked, root0Node15Step1Chunk7_5_checked, root0Node15Step1Chunk8_0_checked, root0Node15Step1Chunk8_1_checked, root0Node15Step1Chunk8_2_checked, root0Node15Step1Chunk8_3_checked, root0Node15Step1Chunk8_4_checked, root0Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node16Domains0 : Domains 37 State := restrict root0Node15Domains1 6 (3,1)
def root0Node16Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,0),(2,4),(4,4)]
  | 3 => some [(0,0),(1,3),(7,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node16Domains0_fast_eq : root0Node16Domains0 = expandDomains root0Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node16Domains0 v = expandDomains root0Node16Domains0Fast v from by decide) v
def root0Node16Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,0)]
  | 3 => [(7,3)]
  | 4 => [(7,5)]
  | 5 => [(6,0)]
  | 6 => [(3,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(7,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(1,0)]
  | 14 => [(7,1)]
  | 15 => [(0,1),(6,4)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(4,0)]
  | 21 => [(7,3)]
  | 22 => [(0,3),(1,0)]
  | 23 => [(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,3)]
  | 34 => [(4,4),(7,2)]
  | 35 => [(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,3)]
def root0Node16Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,0)]
  | 3 => some [(7,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node16Domains1_fast_eq : root0Node16Domains1 = expandDomains root0Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node16Domains1 v = expandDomains root0Node16Domains1Fast v from by decide) v
theorem root0Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root0Node16Domains0 root0Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node16Domains0 root0Node16Domains1
    root0Node16Domains0Fast root0Node16Domains1Fast
    root0Node16Domains0_fast_eq root0Node16Domains1_fast_eq (by decide)
theorem root0Node16Step1_checked :
    checkReplacement table13 root0Node16Domains0 root0Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node16Step1Chunk0_0_checked, root0Node16Step1Chunk0_1_checked, root0Node16Step1Chunk0_2_checked, root0Node16Step1Chunk0_3_checked, root0Node16Step1Chunk0_4_checked, root0Node16Step1Chunk0_5_checked, root0Node16Step1Chunk1_0_checked, root0Node16Step1Chunk1_1_checked, root0Node16Step1Chunk1_2_checked, root0Node16Step1Chunk1_3_checked, root0Node16Step1Chunk1_4_checked, root0Node16Step1Chunk1_5_checked, root0Node16Step1Chunk2_0_checked, root0Node16Step1Chunk2_1_checked, root0Node16Step1Chunk2_2_checked, root0Node16Step1Chunk2_3_checked, root0Node16Step1Chunk2_4_checked, root0Node16Step1Chunk2_5_checked, root0Node16Step1Chunk3_0_checked, root0Node16Step1Chunk3_1_checked, root0Node16Step1Chunk3_2_checked, root0Node16Step1Chunk3_3_checked, root0Node16Step1Chunk3_4_checked, root0Node16Step1Chunk3_5_checked, root0Node16Step1Chunk4_0_checked, root0Node16Step1Chunk4_1_checked, root0Node16Step1Chunk4_2_checked, root0Node16Step1Chunk4_3_checked, root0Node16Step1Chunk4_4_checked, root0Node16Step1Chunk4_5_checked, root0Node16Step1Chunk5_0_checked, root0Node16Step1Chunk5_1_checked, root0Node16Step1Chunk5_2_checked, root0Node16Step1Chunk5_3_checked, root0Node16Step1Chunk5_4_checked, root0Node16Step1Chunk5_5_checked, root0Node16Step1Chunk6_0_checked, root0Node16Step1Chunk6_1_checked, root0Node16Step1Chunk6_2_checked, root0Node16Step1Chunk6_3_checked, root0Node16Step1Chunk6_4_checked, root0Node16Step1Chunk6_5_checked, root0Node16Step1Chunk7_0_checked, root0Node16Step1Chunk7_1_checked, root0Node16Step1Chunk7_2_checked, root0Node16Step1Chunk7_3_checked, root0Node16Step1Chunk7_4_checked, root0Node16Step1Chunk7_5_checked, root0Node16Step1Chunk8_0_checked, root0Node16Step1Chunk8_1_checked, root0Node16Step1Chunk8_2_checked, root0Node16Step1Chunk8_3_checked, root0Node16Step1Chunk8_4_checked, root0Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
