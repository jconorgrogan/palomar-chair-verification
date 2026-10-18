module

public import SpectreFinite.RadiusThreeRoot6Part11
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node21Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(0,4)]
  | 10 => [(5,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(6,5)]
  | 29 => [(0,4)]
  | 30 => [(5,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root6Node21Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(6,5)]
  | 29 => some [(0,4)]
  | 30 => some [(5,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node21Domains2_fast_eq : root6Node21Domains2 = expandDomains root6Node21Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node21Domains2 v = expandDomains root6Node21Domains2Fast v from by decide) v
theorem root6Node21Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node21Domains1 root6Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node21Domains1 root6Node21Domains2
    root6Node21Domains1Fast root6Node21Domains2Fast
    root6Node21Domains1_fast_eq root6Node21Domains2_fast_eq (by decide)
theorem root6Node21Step2_checked :
    checkReplacement table23 root6Node21Domains1 root6Node21Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node21Step2Chunk0_0_checked, root6Node21Step2Chunk0_1_checked, root6Node21Step2Chunk0_2_checked, root6Node21Step2Chunk0_3_checked, root6Node21Step2Chunk0_4_checked, root6Node21Step2Chunk0_5_checked, root6Node21Step2Chunk1_0_checked, root6Node21Step2Chunk1_1_checked, root6Node21Step2Chunk1_2_checked, root6Node21Step2Chunk1_3_checked, root6Node21Step2Chunk1_4_checked, root6Node21Step2Chunk1_5_checked, root6Node21Step2Chunk2_0_checked, root6Node21Step2Chunk2_1_checked, root6Node21Step2Chunk2_2_checked, root6Node21Step2Chunk2_3_checked, root6Node21Step2Chunk2_4_checked, root6Node21Step2Chunk2_5_checked, root6Node21Step2Chunk3_0_checked, root6Node21Step2Chunk3_1_checked, root6Node21Step2Chunk3_2_checked, root6Node21Step2Chunk3_3_checked, root6Node21Step2Chunk3_4_checked, root6Node21Step2Chunk3_5_checked, root6Node21Step2Chunk4_0_checked, root6Node21Step2Chunk4_1_checked, root6Node21Step2Chunk4_2_checked, root6Node21Step2Chunk4_3_checked, root6Node21Step2Chunk4_4_checked, root6Node21Step2Chunk4_5_checked, root6Node21Step2Chunk5_0_checked, root6Node21Step2Chunk5_1_checked, root6Node21Step2Chunk5_2_checked, root6Node21Step2Chunk5_3_checked, root6Node21Step2Chunk5_4_checked, root6Node21Step2Chunk5_5_checked, root6Node21Step2Chunk6_0_checked, root6Node21Step2Chunk6_1_checked, root6Node21Step2Chunk6_2_checked, root6Node21Step2Chunk6_3_checked, root6Node21Step2Chunk6_4_checked, root6Node21Step2Chunk6_5_checked, root6Node21Step2Chunk7_0_checked, root6Node21Step2Chunk7_1_checked, root6Node21Step2Chunk7_2_checked, root6Node21Step2Chunk7_3_checked, root6Node21Step2Chunk7_4_checked, root6Node21Step2Chunk7_5_checked, root6Node21Step2Chunk8_0_checked, root6Node21Step2Chunk8_1_checked, root6Node21Step2Chunk8_2_checked, root6Node21Step2Chunk8_3_checked, root6Node21Step2Chunk8_4_checked, root6Node21Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node21Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node21Domains2 (.output 9) = true := by decide
def root6Node22Domains0 : Domains 37 State := restrict root6Node20Domains1 14 (6,4)
def root6Node22Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root6Node22Domains0_fast_eq : root6Node22Domains0 = expandDomains root6Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node22Domains0 v = expandDomains root6Node22Domains0Fast v from by decide) v
def root6Node22Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(0,4)]
  | 10 => [(5,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(7,4)]
  | 23 => [(1,3),(6,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(8,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(0,2),(6,5)]
  | 29 => [(0,4),(1,1)]
  | 30 => [(5,1),(5,4)]
  | 31 => [(0,1),(6,4)]
  | 32 => [(1,2),(6,2)]
  | 33 => [(7,0),(8,0)]
  | 34 => [(4,3),(8,3)]
  | 35 => [(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0)]
def root6Node22Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3),(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root6Node22Domains1_fast_eq : root6Node22Domains1 = expandDomains root6Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node22Domains1 v = expandDomains root6Node22Domains1Fast v from by decide) v
theorem root6Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node22Domains0 root6Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node22Domains0 root6Node22Domains1
    root6Node22Domains0Fast root6Node22Domains1Fast
    root6Node22Domains0_fast_eq root6Node22Domains1_fast_eq (by decide)
theorem root6Node22Step1_checked :
    checkReplacement table13 root6Node22Domains0 root6Node22Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node22Step1Chunk0_0_checked, root6Node22Step1Chunk0_1_checked, root6Node22Step1Chunk0_2_checked, root6Node22Step1Chunk0_3_checked, root6Node22Step1Chunk0_4_checked, root6Node22Step1Chunk0_5_checked, root6Node22Step1Chunk1_0_checked, root6Node22Step1Chunk1_1_checked, root6Node22Step1Chunk1_2_checked, root6Node22Step1Chunk1_3_checked, root6Node22Step1Chunk1_4_checked, root6Node22Step1Chunk1_5_checked, root6Node22Step1Chunk2_0_checked, root6Node22Step1Chunk2_1_checked, root6Node22Step1Chunk2_2_checked, root6Node22Step1Chunk2_3_checked, root6Node22Step1Chunk2_4_checked, root6Node22Step1Chunk2_5_checked, root6Node22Step1Chunk3_0_checked, root6Node22Step1Chunk3_1_checked, root6Node22Step1Chunk3_2_checked, root6Node22Step1Chunk3_3_checked, root6Node22Step1Chunk3_4_checked, root6Node22Step1Chunk3_5_checked, root6Node22Step1Chunk4_0_checked, root6Node22Step1Chunk4_1_checked, root6Node22Step1Chunk4_2_checked, root6Node22Step1Chunk4_3_checked, root6Node22Step1Chunk4_4_checked, root6Node22Step1Chunk4_5_checked, root6Node22Step1Chunk5_0_checked, root6Node22Step1Chunk5_1_checked, root6Node22Step1Chunk5_2_checked, root6Node22Step1Chunk5_3_checked, root6Node22Step1Chunk5_4_checked, root6Node22Step1Chunk5_5_checked, root6Node22Step1Chunk6_0_checked, root6Node22Step1Chunk6_1_checked, root6Node22Step1Chunk6_2_checked, root6Node22Step1Chunk6_3_checked, root6Node22Step1Chunk6_4_checked, root6Node22Step1Chunk6_5_checked, root6Node22Step1Chunk7_0_checked, root6Node22Step1Chunk7_1_checked, root6Node22Step1Chunk7_2_checked, root6Node22Step1Chunk7_3_checked, root6Node22Step1Chunk7_4_checked, root6Node22Step1Chunk7_5_checked, root6Node22Step1Chunk8_0_checked, root6Node22Step1Chunk8_1_checked, root6Node22Step1Chunk8_2_checked, root6Node22Step1Chunk8_3_checked, root6Node22Step1Chunk8_4_checked, root6Node22Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node23Domains0 : Domains 37 State := restrict root6Node22Domains1 23 (1,3)
def root6Node23Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root6Node23Domains0_fast_eq : root6Node23Domains0 = expandDomains root6Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node23Domains0 v = expandDomains root6Node23Domains0Fast v from by decide) v
def root6Node23Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(0,4)]
  | 10 => [(5,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(6,4)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(6,5)]
  | 29 => [(0,4)]
  | 30 => [(5,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(3,5),(7,5)]
  | _ => [(0,3)]
def root6Node23Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(0,4)]
  | 10 => some [(5,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(6,5)]
  | 29 => some [(0,4)]
  | 30 => some [(5,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root6Node23Domains1_fast_eq : root6Node23Domains1 = expandDomains root6Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node23Domains1 v = expandDomains root6Node23Domains1Fast v from by decide) v
theorem root6Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root6Node23Domains0 root6Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node23Domains0 root6Node23Domains1
    root6Node23Domains0Fast root6Node23Domains1Fast
    root6Node23Domains0_fast_eq root6Node23Domains1_fast_eq (by decide)
theorem root6Node23Step1_checked :
    checkReplacement table30 root6Node23Domains0 root6Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node23Step1Chunk0_0_checked, root6Node23Step1Chunk0_1_checked, root6Node23Step1Chunk0_2_checked, root6Node23Step1Chunk0_3_checked, root6Node23Step1Chunk0_4_checked, root6Node23Step1Chunk0_5_checked, root6Node23Step1Chunk1_0_checked, root6Node23Step1Chunk1_1_checked, root6Node23Step1Chunk1_2_checked, root6Node23Step1Chunk1_3_checked, root6Node23Step1Chunk1_4_checked, root6Node23Step1Chunk1_5_checked, root6Node23Step1Chunk2_0_checked, root6Node23Step1Chunk2_1_checked, root6Node23Step1Chunk2_2_checked, root6Node23Step1Chunk2_3_checked, root6Node23Step1Chunk2_4_checked, root6Node23Step1Chunk2_5_checked, root6Node23Step1Chunk3_0_checked, root6Node23Step1Chunk3_1_checked, root6Node23Step1Chunk3_2_checked, root6Node23Step1Chunk3_3_checked, root6Node23Step1Chunk3_4_checked, root6Node23Step1Chunk3_5_checked, root6Node23Step1Chunk4_0_checked, root6Node23Step1Chunk4_1_checked, root6Node23Step1Chunk4_2_checked, root6Node23Step1Chunk4_3_checked, root6Node23Step1Chunk4_4_checked, root6Node23Step1Chunk4_5_checked, root6Node23Step1Chunk5_0_checked, root6Node23Step1Chunk5_1_checked, root6Node23Step1Chunk5_2_checked, root6Node23Step1Chunk5_3_checked, root6Node23Step1Chunk5_4_checked, root6Node23Step1Chunk5_5_checked, root6Node23Step1Chunk6_0_checked, root6Node23Step1Chunk6_1_checked, root6Node23Step1Chunk6_2_checked, root6Node23Step1Chunk6_3_checked, root6Node23Step1Chunk6_4_checked, root6Node23Step1Chunk6_5_checked, root6Node23Step1Chunk7_0_checked, root6Node23Step1Chunk7_1_checked, root6Node23Step1Chunk7_2_checked, root6Node23Step1Chunk7_3_checked, root6Node23Step1Chunk7_4_checked, root6Node23Step1Chunk7_5_checked, root6Node23Step1Chunk8_0_checked, root6Node23Step1Chunk8_1_checked, root6Node23Step1Chunk8_2_checked, root6Node23Step1Chunk8_3_checked, root6Node23Step1Chunk8_4_checked, root6Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
