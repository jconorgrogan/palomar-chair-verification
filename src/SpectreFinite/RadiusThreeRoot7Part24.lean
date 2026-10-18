module

public import SpectreFinite.RadiusThreeRoot7Part23
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable15
public import SpectreFinite.RadiusThreeTable24
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node35Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1)]
  | 14 => [(0,2)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(8,4)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3)]
  | 32 => [(8,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2)]
  | _ => [(5,3)]
def root7Node35Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1)]
  | 14 => some [(0,2)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root7Node35Domains3_fast_eq : root7Node35Domains3 = expandDomains root7Node35Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node35Domains3 v = expandDomains root7Node35Domains3Fast v from by decide) v
theorem root7Node35Step3Chunk0_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk0_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk0_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk0_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk0_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk0_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows0_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk1_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk1_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk1_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk1_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk1_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk1_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows1_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk2_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk2_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk2_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk2_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk2_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk2_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows2_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk3_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk3_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk3_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk3_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk3_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk3_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows3_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk4_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk4_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk4_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk4_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk4_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk4_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows4_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk5_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk5_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk5_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk5_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk5_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk5_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows5_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk6_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk6_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk6_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk6_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk6_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk6_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows6_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk7_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk7_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk7_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk7_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk7_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk7_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows7_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk8_0_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_0⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk8_1_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_1⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk8_2_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_2⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk8_3_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_3⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk8_4_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_4⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3Chunk8_5_checked :
    checkNarrowing ⟨table15Scope, table15Rows8_5⟩
      root7Node35Domains2 root7Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains2 root7Node35Domains3
    root7Node35Domains2Fast root7Node35Domains3Fast
    root7Node35Domains2_fast_eq root7Node35Domains3_fast_eq (by decide)
theorem root7Node35Step3_checked :
    checkReplacement table15 root7Node35Domains2 root7Node35Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node35Step3Chunk0_0_checked, root7Node35Step3Chunk0_1_checked, root7Node35Step3Chunk0_2_checked, root7Node35Step3Chunk0_3_checked, root7Node35Step3Chunk0_4_checked, root7Node35Step3Chunk0_5_checked, root7Node35Step3Chunk1_0_checked, root7Node35Step3Chunk1_1_checked, root7Node35Step3Chunk1_2_checked, root7Node35Step3Chunk1_3_checked, root7Node35Step3Chunk1_4_checked, root7Node35Step3Chunk1_5_checked, root7Node35Step3Chunk2_0_checked, root7Node35Step3Chunk2_1_checked, root7Node35Step3Chunk2_2_checked, root7Node35Step3Chunk2_3_checked, root7Node35Step3Chunk2_4_checked, root7Node35Step3Chunk2_5_checked, root7Node35Step3Chunk3_0_checked, root7Node35Step3Chunk3_1_checked, root7Node35Step3Chunk3_2_checked, root7Node35Step3Chunk3_3_checked, root7Node35Step3Chunk3_4_checked, root7Node35Step3Chunk3_5_checked, root7Node35Step3Chunk4_0_checked, root7Node35Step3Chunk4_1_checked, root7Node35Step3Chunk4_2_checked, root7Node35Step3Chunk4_3_checked, root7Node35Step3Chunk4_4_checked, root7Node35Step3Chunk4_5_checked, root7Node35Step3Chunk5_0_checked, root7Node35Step3Chunk5_1_checked, root7Node35Step3Chunk5_2_checked, root7Node35Step3Chunk5_3_checked, root7Node35Step3Chunk5_4_checked, root7Node35Step3Chunk5_5_checked, root7Node35Step3Chunk6_0_checked, root7Node35Step3Chunk6_1_checked, root7Node35Step3Chunk6_2_checked, root7Node35Step3Chunk6_3_checked, root7Node35Step3Chunk6_4_checked, root7Node35Step3Chunk6_5_checked, root7Node35Step3Chunk7_0_checked, root7Node35Step3Chunk7_1_checked, root7Node35Step3Chunk7_2_checked, root7Node35Step3Chunk7_3_checked, root7Node35Step3Chunk7_4_checked, root7Node35Step3Chunk7_5_checked, root7Node35Step3Chunk8_0_checked, root7Node35Step3Chunk8_1_checked, root7Node35Step3Chunk8_2_checked, root7Node35Step3Chunk8_3_checked, root7Node35Step3Chunk8_4_checked, root7Node35Step3Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node35Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node35Domains3 (.output 16) = true := by decide
def root7Node36Domains0 : Domains 37 State := restrict root7Node34Domains2 13 (8,1)
def root7Node36Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(6,3)]
  | 27 => some [(4,4),(7,2),(8,4)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5)]
  | 31 => some [(0,2),(0,3),(6,0)]
  | 32 => some [(1,1),(7,1),(8,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(5,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root7Node36Domains0_fast_eq : root7Node36Domains0 = expandDomains root7Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node36Domains0 v = expandDomains root7Node36Domains0Fast v from by decide) v
def root7Node36Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5),(8,5)]
  | 21 => [(3,0),(7,0)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(6,3)]
  | 27 => [(4,4),(7,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5)]
  | 31 => [(0,2),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(5,2),(8,2)]
  | _ => [(5,0),(8,0)]
def root7Node36Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(3,0),(7,0)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(4,4),(7,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5)]
  | 31 => some [(0,2),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2),(8,2)]
  | _ => some [(5,0),(8,0)]
theorem root7Node36Domains1_fast_eq : root7Node36Domains1 = expandDomains root7Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node36Domains1 v = expandDomains root7Node36Domains1Fast v from by decide) v
theorem root7Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1_checked :
    checkReplacement table26 root7Node36Domains0 root7Node36Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node36Step1Chunk0_0_checked, root7Node36Step1Chunk0_1_checked, root7Node36Step1Chunk0_2_checked, root7Node36Step1Chunk0_3_checked, root7Node36Step1Chunk0_4_checked, root7Node36Step1Chunk0_5_checked, root7Node36Step1Chunk1_0_checked, root7Node36Step1Chunk1_1_checked, root7Node36Step1Chunk1_2_checked, root7Node36Step1Chunk1_3_checked, root7Node36Step1Chunk1_4_checked, root7Node36Step1Chunk1_5_checked, root7Node36Step1Chunk2_0_checked, root7Node36Step1Chunk2_1_checked, root7Node36Step1Chunk2_2_checked, root7Node36Step1Chunk2_3_checked, root7Node36Step1Chunk2_4_checked, root7Node36Step1Chunk2_5_checked, root7Node36Step1Chunk3_0_checked, root7Node36Step1Chunk3_1_checked, root7Node36Step1Chunk3_2_checked, root7Node36Step1Chunk3_3_checked, root7Node36Step1Chunk3_4_checked, root7Node36Step1Chunk3_5_checked, root7Node36Step1Chunk4_0_checked, root7Node36Step1Chunk4_1_checked, root7Node36Step1Chunk4_2_checked, root7Node36Step1Chunk4_3_checked, root7Node36Step1Chunk4_4_checked, root7Node36Step1Chunk4_5_checked, root7Node36Step1Chunk5_0_checked, root7Node36Step1Chunk5_1_checked, root7Node36Step1Chunk5_2_checked, root7Node36Step1Chunk5_3_checked, root7Node36Step1Chunk5_4_checked, root7Node36Step1Chunk5_5_checked, root7Node36Step1Chunk6_0_checked, root7Node36Step1Chunk6_1_checked, root7Node36Step1Chunk6_2_checked, root7Node36Step1Chunk6_3_checked, root7Node36Step1Chunk6_4_checked, root7Node36Step1Chunk6_5_checked, root7Node36Step1Chunk7_0_checked, root7Node36Step1Chunk7_1_checked, root7Node36Step1Chunk7_2_checked, root7Node36Step1Chunk7_3_checked, root7Node36Step1Chunk7_4_checked, root7Node36Step1Chunk7_5_checked, root7Node36Step1Chunk8_0_checked, root7Node36Step1Chunk8_1_checked, root7Node36Step1Chunk8_2_checked, root7Node36Step1Chunk8_3_checked, root7Node36Step1Chunk8_4_checked, root7Node36Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node37Domains0 : Domains 37 State := restrict root7Node36Domains1 17 (5,5)
def root7Node37Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(3,0),(7,0)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(4,4),(7,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5)]
  | 31 => some [(0,2),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2),(8,2)]
  | _ => some [(5,0),(8,0)]
theorem root7Node37Domains0_fast_eq : root7Node37Domains0 = expandDomains root7Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node37Domains0 v = expandDomains root7Node37Domains0Fast v from by decide) v
def root7Node37Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(8,1)]
  | 14 => [(6,5)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5),(8,5)]
  | 21 => [(3,0),(7,0)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4),(7,2)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0),(8,0)]
def root7Node37Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(3,0),(7,0)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4),(7,2)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0),(8,0)]
theorem root7Node37Domains1_fast_eq : root7Node37Domains1 = expandDomains root7Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node37Domains1 v = expandDomains root7Node37Domains1Fast v from by decide) v
theorem root7Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1_checked :
    checkReplacement table24 root7Node37Domains0 root7Node37Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node37Step1Chunk0_0_checked, root7Node37Step1Chunk0_1_checked, root7Node37Step1Chunk0_2_checked, root7Node37Step1Chunk0_3_checked, root7Node37Step1Chunk0_4_checked, root7Node37Step1Chunk0_5_checked, root7Node37Step1Chunk1_0_checked, root7Node37Step1Chunk1_1_checked, root7Node37Step1Chunk1_2_checked, root7Node37Step1Chunk1_3_checked, root7Node37Step1Chunk1_4_checked, root7Node37Step1Chunk1_5_checked, root7Node37Step1Chunk2_0_checked, root7Node37Step1Chunk2_1_checked, root7Node37Step1Chunk2_2_checked, root7Node37Step1Chunk2_3_checked, root7Node37Step1Chunk2_4_checked, root7Node37Step1Chunk2_5_checked, root7Node37Step1Chunk3_0_checked, root7Node37Step1Chunk3_1_checked, root7Node37Step1Chunk3_2_checked, root7Node37Step1Chunk3_3_checked, root7Node37Step1Chunk3_4_checked, root7Node37Step1Chunk3_5_checked, root7Node37Step1Chunk4_0_checked, root7Node37Step1Chunk4_1_checked, root7Node37Step1Chunk4_2_checked, root7Node37Step1Chunk4_3_checked, root7Node37Step1Chunk4_4_checked, root7Node37Step1Chunk4_5_checked, root7Node37Step1Chunk5_0_checked, root7Node37Step1Chunk5_1_checked, root7Node37Step1Chunk5_2_checked, root7Node37Step1Chunk5_3_checked, root7Node37Step1Chunk5_4_checked, root7Node37Step1Chunk5_5_checked, root7Node37Step1Chunk6_0_checked, root7Node37Step1Chunk6_1_checked, root7Node37Step1Chunk6_2_checked, root7Node37Step1Chunk6_3_checked, root7Node37Step1Chunk6_4_checked, root7Node37Step1Chunk6_5_checked, root7Node37Step1Chunk7_0_checked, root7Node37Step1Chunk7_1_checked, root7Node37Step1Chunk7_2_checked, root7Node37Step1Chunk7_3_checked, root7Node37Step1Chunk7_4_checked, root7Node37Step1Chunk7_5_checked, root7Node37Step1Chunk8_0_checked, root7Node37Step1Chunk8_1_checked, root7Node37Step1Chunk8_2_checked, root7Node37Step1Chunk8_3_checked, root7Node37Step1Chunk8_4_checked, root7Node37Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
