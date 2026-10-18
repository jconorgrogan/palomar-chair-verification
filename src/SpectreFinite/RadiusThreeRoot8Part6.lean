module

public import SpectreFinite.RadiusThreeRoot8Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node7Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(2,2),(2,4)]
  | 16 => [(1,3),(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(5,4),(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(1,0),(7,0)]
  | 29 => [(4,3),(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(8,1)]
  | 33 => [(4,0),(7,4)]
  | 34 => [(1,3),(7,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root8Node7Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(2,2),(2,4)]
  | 16 => some [(1,3),(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(4,0),(7,4)]
  | 34 => some [(1,3),(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node7Domains2_fast_eq : root8Node7Domains2 = expandDomains root8Node7Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node7Domains2 v = expandDomains root8Node7Domains2Fast v from by decide) v
theorem root8Node7Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node7Domains1 root8Node7Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node7Domains1 root8Node7Domains2
    root8Node7Domains1Fast root8Node7Domains2Fast
    root8Node7Domains1_fast_eq root8Node7Domains2_fast_eq (by decide)
theorem root8Node7Step2_checked :
    checkReplacement table23 root8Node7Domains1 root8Node7Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node7Step2Chunk0_0_checked, root8Node7Step2Chunk0_1_checked, root8Node7Step2Chunk0_2_checked, root8Node7Step2Chunk0_3_checked, root8Node7Step2Chunk0_4_checked, root8Node7Step2Chunk0_5_checked, root8Node7Step2Chunk1_0_checked, root8Node7Step2Chunk1_1_checked, root8Node7Step2Chunk1_2_checked, root8Node7Step2Chunk1_3_checked, root8Node7Step2Chunk1_4_checked, root8Node7Step2Chunk1_5_checked, root8Node7Step2Chunk2_0_checked, root8Node7Step2Chunk2_1_checked, root8Node7Step2Chunk2_2_checked, root8Node7Step2Chunk2_3_checked, root8Node7Step2Chunk2_4_checked, root8Node7Step2Chunk2_5_checked, root8Node7Step2Chunk3_0_checked, root8Node7Step2Chunk3_1_checked, root8Node7Step2Chunk3_2_checked, root8Node7Step2Chunk3_3_checked, root8Node7Step2Chunk3_4_checked, root8Node7Step2Chunk3_5_checked, root8Node7Step2Chunk4_0_checked, root8Node7Step2Chunk4_1_checked, root8Node7Step2Chunk4_2_checked, root8Node7Step2Chunk4_3_checked, root8Node7Step2Chunk4_4_checked, root8Node7Step2Chunk4_5_checked, root8Node7Step2Chunk5_0_checked, root8Node7Step2Chunk5_1_checked, root8Node7Step2Chunk5_2_checked, root8Node7Step2Chunk5_3_checked, root8Node7Step2Chunk5_4_checked, root8Node7Step2Chunk5_5_checked, root8Node7Step2Chunk6_0_checked, root8Node7Step2Chunk6_1_checked, root8Node7Step2Chunk6_2_checked, root8Node7Step2Chunk6_3_checked, root8Node7Step2Chunk6_4_checked, root8Node7Step2Chunk6_5_checked, root8Node7Step2Chunk7_0_checked, root8Node7Step2Chunk7_1_checked, root8Node7Step2Chunk7_2_checked, root8Node7Step2Chunk7_3_checked, root8Node7Step2Chunk7_4_checked, root8Node7Step2Chunk7_5_checked, root8Node7Step2Chunk8_0_checked, root8Node7Step2Chunk8_1_checked, root8Node7Step2Chunk8_2_checked, root8Node7Step2Chunk8_3_checked, root8Node7Step2Chunk8_4_checked, root8Node7Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node8Domains0 : Domains 37 State := restrict root8Node7Domains2 15 (2,2)
def root8Node8Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(2,2)]
  | 16 => some [(1,3),(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(4,0),(7,4)]
  | 34 => some [(1,3),(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node8Domains0_fast_eq : root8Node8Domains0 = expandDomains root8Node8Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node8Domains0 v = expandDomains root8Node8Domains0Fast v from by decide) v
def root8Node8Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(8,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root8Node8Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node8Domains1_fast_eq : root8Node8Domains1 = expandDomains root8Node8Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node8Domains1 v = expandDomains root8Node8Domains1Fast v from by decide) v
theorem root8Node8Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node8Domains0 root8Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node8Domains0 root8Node8Domains1
    root8Node8Domains0Fast root8Node8Domains1Fast
    root8Node8Domains0_fast_eq root8Node8Domains1_fast_eq (by decide)
theorem root8Node8Step1_checked :
    checkReplacement table23 root8Node8Domains0 root8Node8Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node8Step1Chunk0_0_checked, root8Node8Step1Chunk0_1_checked, root8Node8Step1Chunk0_2_checked, root8Node8Step1Chunk0_3_checked, root8Node8Step1Chunk0_4_checked, root8Node8Step1Chunk0_5_checked, root8Node8Step1Chunk1_0_checked, root8Node8Step1Chunk1_1_checked, root8Node8Step1Chunk1_2_checked, root8Node8Step1Chunk1_3_checked, root8Node8Step1Chunk1_4_checked, root8Node8Step1Chunk1_5_checked, root8Node8Step1Chunk2_0_checked, root8Node8Step1Chunk2_1_checked, root8Node8Step1Chunk2_2_checked, root8Node8Step1Chunk2_3_checked, root8Node8Step1Chunk2_4_checked, root8Node8Step1Chunk2_5_checked, root8Node8Step1Chunk3_0_checked, root8Node8Step1Chunk3_1_checked, root8Node8Step1Chunk3_2_checked, root8Node8Step1Chunk3_3_checked, root8Node8Step1Chunk3_4_checked, root8Node8Step1Chunk3_5_checked, root8Node8Step1Chunk4_0_checked, root8Node8Step1Chunk4_1_checked, root8Node8Step1Chunk4_2_checked, root8Node8Step1Chunk4_3_checked, root8Node8Step1Chunk4_4_checked, root8Node8Step1Chunk4_5_checked, root8Node8Step1Chunk5_0_checked, root8Node8Step1Chunk5_1_checked, root8Node8Step1Chunk5_2_checked, root8Node8Step1Chunk5_3_checked, root8Node8Step1Chunk5_4_checked, root8Node8Step1Chunk5_5_checked, root8Node8Step1Chunk6_0_checked, root8Node8Step1Chunk6_1_checked, root8Node8Step1Chunk6_2_checked, root8Node8Step1Chunk6_3_checked, root8Node8Step1Chunk6_4_checked, root8Node8Step1Chunk6_5_checked, root8Node8Step1Chunk7_0_checked, root8Node8Step1Chunk7_1_checked, root8Node8Step1Chunk7_2_checked, root8Node8Step1Chunk7_3_checked, root8Node8Step1Chunk7_4_checked, root8Node8Step1Chunk7_5_checked, root8Node8Step1Chunk8_0_checked, root8Node8Step1Chunk8_1_checked, root8Node8Step1Chunk8_2_checked, root8Node8Step1Chunk8_3_checked, root8Node8Step1Chunk8_4_checked, root8Node8Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node8Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node8Domains1 (.output 2) = true := by decide
def root8Node9Domains0 : Domains 37 State := restrict root8Node7Domains2 15 (2,4)
def root8Node9Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3),(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(5,4),(8,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(1,0),(7,0)]
  | 29 => some [(4,3),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(4,0),(7,4)]
  | 34 => some [(1,3),(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node9Domains0_fast_eq : root8Node9Domains0 = expandDomains root8Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node9Domains0 v = expandDomains root8Node9Domains0Fast v from by decide) v
def root8Node9Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(8,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root8Node9Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node9Domains1_fast_eq : root8Node9Domains1 = expandDomains root8Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node9Domains1 v = expandDomains root8Node9Domains1Fast v from by decide) v
theorem root8Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1_checked :
    checkReplacement table23 root8Node9Domains0 root8Node9Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node9Step1Chunk0_0_checked, root8Node9Step1Chunk0_1_checked, root8Node9Step1Chunk0_2_checked, root8Node9Step1Chunk0_3_checked, root8Node9Step1Chunk0_4_checked, root8Node9Step1Chunk0_5_checked, root8Node9Step1Chunk1_0_checked, root8Node9Step1Chunk1_1_checked, root8Node9Step1Chunk1_2_checked, root8Node9Step1Chunk1_3_checked, root8Node9Step1Chunk1_4_checked, root8Node9Step1Chunk1_5_checked, root8Node9Step1Chunk2_0_checked, root8Node9Step1Chunk2_1_checked, root8Node9Step1Chunk2_2_checked, root8Node9Step1Chunk2_3_checked, root8Node9Step1Chunk2_4_checked, root8Node9Step1Chunk2_5_checked, root8Node9Step1Chunk3_0_checked, root8Node9Step1Chunk3_1_checked, root8Node9Step1Chunk3_2_checked, root8Node9Step1Chunk3_3_checked, root8Node9Step1Chunk3_4_checked, root8Node9Step1Chunk3_5_checked, root8Node9Step1Chunk4_0_checked, root8Node9Step1Chunk4_1_checked, root8Node9Step1Chunk4_2_checked, root8Node9Step1Chunk4_3_checked, root8Node9Step1Chunk4_4_checked, root8Node9Step1Chunk4_5_checked, root8Node9Step1Chunk5_0_checked, root8Node9Step1Chunk5_1_checked, root8Node9Step1Chunk5_2_checked, root8Node9Step1Chunk5_3_checked, root8Node9Step1Chunk5_4_checked, root8Node9Step1Chunk5_5_checked, root8Node9Step1Chunk6_0_checked, root8Node9Step1Chunk6_1_checked, root8Node9Step1Chunk6_2_checked, root8Node9Step1Chunk6_3_checked, root8Node9Step1Chunk6_4_checked, root8Node9Step1Chunk6_5_checked, root8Node9Step1Chunk7_0_checked, root8Node9Step1Chunk7_1_checked, root8Node9Step1Chunk7_2_checked, root8Node9Step1Chunk7_3_checked, root8Node9Step1Chunk7_4_checked, root8Node9Step1Chunk7_5_checked, root8Node9Step1Chunk8_0_checked, root8Node9Step1Chunk8_1_checked, root8Node9Step1Chunk8_2_checked, root8Node9Step1Chunk8_3_checked, root8Node9Step1Chunk8_4_checked, root8Node9Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node9Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node9Domains1 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
