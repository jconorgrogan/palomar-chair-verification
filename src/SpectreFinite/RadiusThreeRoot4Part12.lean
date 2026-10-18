module

public import SpectreFinite.RadiusThreeRoot4Part11
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node21Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5),(8,5)]
  | 3 => [(7,0)]
  | 4 => [(5,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4),(7,2)]
  | 8 => [(1,4),(6,4),(7,4)]
  | 9 => [(4,3)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,2),(0,3),(6,0)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,0),(5,3),(8,0)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(4,2),(7,0),(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node21Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5),(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4),(7,2)]
  | 8 => some [(1,4),(6,4),(7,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,2),(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(4,2),(7,0),(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node21Domains2_fast_eq : root4Node21Domains2 = expandDomains root4Node21Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node21Domains2 v = expandDomains root4Node21Domains2Fast v from by decide) v
theorem root4Node21Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root4Node21Domains1 root4Node21Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains1 root4Node21Domains2
    root4Node21Domains1Fast root4Node21Domains2Fast
    root4Node21Domains1_fast_eq root4Node21Domains2_fast_eq (by decide)
theorem root4Node21Step2_checked :
    checkReplacement table25 root4Node21Domains1 root4Node21Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node21Step2Chunk0_0_checked, root4Node21Step2Chunk0_1_checked, root4Node21Step2Chunk0_2_checked, root4Node21Step2Chunk0_3_checked, root4Node21Step2Chunk0_4_checked, root4Node21Step2Chunk0_5_checked, root4Node21Step2Chunk1_0_checked, root4Node21Step2Chunk1_1_checked, root4Node21Step2Chunk1_2_checked, root4Node21Step2Chunk1_3_checked, root4Node21Step2Chunk1_4_checked, root4Node21Step2Chunk1_5_checked, root4Node21Step2Chunk2_0_checked, root4Node21Step2Chunk2_1_checked, root4Node21Step2Chunk2_2_checked, root4Node21Step2Chunk2_3_checked, root4Node21Step2Chunk2_4_checked, root4Node21Step2Chunk2_5_checked, root4Node21Step2Chunk3_0_checked, root4Node21Step2Chunk3_1_checked, root4Node21Step2Chunk3_2_checked, root4Node21Step2Chunk3_3_checked, root4Node21Step2Chunk3_4_checked, root4Node21Step2Chunk3_5_checked, root4Node21Step2Chunk4_0_checked, root4Node21Step2Chunk4_1_checked, root4Node21Step2Chunk4_2_checked, root4Node21Step2Chunk4_3_checked, root4Node21Step2Chunk4_4_checked, root4Node21Step2Chunk4_5_checked, root4Node21Step2Chunk5_0_checked, root4Node21Step2Chunk5_1_checked, root4Node21Step2Chunk5_2_checked, root4Node21Step2Chunk5_3_checked, root4Node21Step2Chunk5_4_checked, root4Node21Step2Chunk5_5_checked, root4Node21Step2Chunk6_0_checked, root4Node21Step2Chunk6_1_checked, root4Node21Step2Chunk6_2_checked, root4Node21Step2Chunk6_3_checked, root4Node21Step2Chunk6_4_checked, root4Node21Step2Chunk6_5_checked, root4Node21Step2Chunk7_0_checked, root4Node21Step2Chunk7_1_checked, root4Node21Step2Chunk7_2_checked, root4Node21Step2Chunk7_3_checked, root4Node21Step2Chunk7_4_checked, root4Node21Step2Chunk7_5_checked, root4Node21Step2Chunk8_0_checked, root4Node21Step2Chunk8_1_checked, root4Node21Step2Chunk8_2_checked, root4Node21Step2Chunk8_3_checked, root4Node21Step2Chunk8_4_checked, root4Node21Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node21Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(5,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(6,4)]
  | 9 => [(4,3)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(4,2),(7,0),(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node21Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(4,2),(7,0),(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node21Domains3_fast_eq : root4Node21Domains3 = expandDomains root4Node21Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node21Domains3 v = expandDomains root4Node21Domains3Fast v from by decide) v
theorem root4Node21Step3Chunk0_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk0_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk0_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk0_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk0_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk0_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows0_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk1_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk1_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk1_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk1_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk1_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk1_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows1_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk2_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk2_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk2_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk2_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk2_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk2_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows2_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk3_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk3_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk3_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk3_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk3_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk3_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows3_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk4_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk4_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk4_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk4_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk4_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk4_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows4_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk5_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk5_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk5_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk5_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk5_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk5_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows5_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk6_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk6_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk6_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk6_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk6_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk6_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows6_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk7_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk7_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk7_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk7_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk7_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk7_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows7_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk8_0_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_0⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk8_1_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_1⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk8_2_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_2⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk8_3_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_3⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk8_4_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_4⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3Chunk8_5_checked :
    checkNarrowing ⟨table8Scope, table8Rows8_5⟩
      root4Node21Domains2 root4Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains2 root4Node21Domains3
    root4Node21Domains2Fast root4Node21Domains3Fast
    root4Node21Domains2_fast_eq root4Node21Domains3_fast_eq (by decide)
theorem root4Node21Step3_checked :
    checkReplacement table8 root4Node21Domains2 root4Node21Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node21Step3Chunk0_0_checked, root4Node21Step3Chunk0_1_checked, root4Node21Step3Chunk0_2_checked, root4Node21Step3Chunk0_3_checked, root4Node21Step3Chunk0_4_checked, root4Node21Step3Chunk0_5_checked, root4Node21Step3Chunk1_0_checked, root4Node21Step3Chunk1_1_checked, root4Node21Step3Chunk1_2_checked, root4Node21Step3Chunk1_3_checked, root4Node21Step3Chunk1_4_checked, root4Node21Step3Chunk1_5_checked, root4Node21Step3Chunk2_0_checked, root4Node21Step3Chunk2_1_checked, root4Node21Step3Chunk2_2_checked, root4Node21Step3Chunk2_3_checked, root4Node21Step3Chunk2_4_checked, root4Node21Step3Chunk2_5_checked, root4Node21Step3Chunk3_0_checked, root4Node21Step3Chunk3_1_checked, root4Node21Step3Chunk3_2_checked, root4Node21Step3Chunk3_3_checked, root4Node21Step3Chunk3_4_checked, root4Node21Step3Chunk3_5_checked, root4Node21Step3Chunk4_0_checked, root4Node21Step3Chunk4_1_checked, root4Node21Step3Chunk4_2_checked, root4Node21Step3Chunk4_3_checked, root4Node21Step3Chunk4_4_checked, root4Node21Step3Chunk4_5_checked, root4Node21Step3Chunk5_0_checked, root4Node21Step3Chunk5_1_checked, root4Node21Step3Chunk5_2_checked, root4Node21Step3Chunk5_3_checked, root4Node21Step3Chunk5_4_checked, root4Node21Step3Chunk5_5_checked, root4Node21Step3Chunk6_0_checked, root4Node21Step3Chunk6_1_checked, root4Node21Step3Chunk6_2_checked, root4Node21Step3Chunk6_3_checked, root4Node21Step3Chunk6_4_checked, root4Node21Step3Chunk6_5_checked, root4Node21Step3Chunk7_0_checked, root4Node21Step3Chunk7_1_checked, root4Node21Step3Chunk7_2_checked, root4Node21Step3Chunk7_3_checked, root4Node21Step3Chunk7_4_checked, root4Node21Step3Chunk7_5_checked, root4Node21Step3Chunk8_0_checked, root4Node21Step3Chunk8_1_checked, root4Node21Step3Chunk8_2_checked, root4Node21Step3Chunk8_3_checked, root4Node21Step3Chunk8_4_checked, root4Node21Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node21Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(7,0)]
  | 4 => [(5,4)]
  | 5 => [(1,4)]
  | 6 => [(0,5)]
  | 7 => [(4,4)]
  | 8 => [(6,4)]
  | 9 => [(4,3)]
  | 10 => [(7,5)]
  | 11 => [(6,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(0,2)]
  | 23 => [(1,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(7,4)]
  | 28 => [(8,0)]
  | 29 => [(8,3)]
  | 30 => [(5,5)]
  | 31 => [(1,0)]
  | 32 => [(2,1)]
  | 33 => [(1,4)]
  | 34 => [(0,5)]
  | 35 => [(4,4)]
  | _ => [(0,0)]
def root4Node21Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(7,0)]
  | 4 => some [(5,4)]
  | 5 => some [(1,4)]
  | 6 => some [(0,5)]
  | 7 => some [(4,4)]
  | 8 => some [(6,4)]
  | 9 => some [(4,3)]
  | 10 => some [(7,5)]
  | 11 => some [(6,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(0,2)]
  | 23 => some [(1,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4)]
  | 28 => some [(8,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1)]
  | 33 => some [(1,4)]
  | 34 => some [(0,5)]
  | 35 => some [(4,4)]
  | _ => some [(0,0)]
theorem root4Node21Domains4_fast_eq : root4Node21Domains4 = expandDomains root4Node21Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node21Domains4 v = expandDomains root4Node21Domains4Fast v from by decide) v
theorem root4Node21Step4Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root4Node21Domains3 root4Node21Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node21Domains3 root4Node21Domains4
    root4Node21Domains3Fast root4Node21Domains4Fast
    root4Node21Domains3_fast_eq root4Node21Domains4_fast_eq (by decide)
theorem root4Node21Step4_checked :
    checkReplacement table22 root4Node21Domains3 root4Node21Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node21Step4Chunk0_0_checked, root4Node21Step4Chunk0_1_checked, root4Node21Step4Chunk0_2_checked, root4Node21Step4Chunk0_3_checked, root4Node21Step4Chunk0_4_checked, root4Node21Step4Chunk0_5_checked, root4Node21Step4Chunk1_0_checked, root4Node21Step4Chunk1_1_checked, root4Node21Step4Chunk1_2_checked, root4Node21Step4Chunk1_3_checked, root4Node21Step4Chunk1_4_checked, root4Node21Step4Chunk1_5_checked, root4Node21Step4Chunk2_0_checked, root4Node21Step4Chunk2_1_checked, root4Node21Step4Chunk2_2_checked, root4Node21Step4Chunk2_3_checked, root4Node21Step4Chunk2_4_checked, root4Node21Step4Chunk2_5_checked, root4Node21Step4Chunk3_0_checked, root4Node21Step4Chunk3_1_checked, root4Node21Step4Chunk3_2_checked, root4Node21Step4Chunk3_3_checked, root4Node21Step4Chunk3_4_checked, root4Node21Step4Chunk3_5_checked, root4Node21Step4Chunk4_0_checked, root4Node21Step4Chunk4_1_checked, root4Node21Step4Chunk4_2_checked, root4Node21Step4Chunk4_3_checked, root4Node21Step4Chunk4_4_checked, root4Node21Step4Chunk4_5_checked, root4Node21Step4Chunk5_0_checked, root4Node21Step4Chunk5_1_checked, root4Node21Step4Chunk5_2_checked, root4Node21Step4Chunk5_3_checked, root4Node21Step4Chunk5_4_checked, root4Node21Step4Chunk5_5_checked, root4Node21Step4Chunk6_0_checked, root4Node21Step4Chunk6_1_checked, root4Node21Step4Chunk6_2_checked, root4Node21Step4Chunk6_3_checked, root4Node21Step4Chunk6_4_checked, root4Node21Step4Chunk6_5_checked, root4Node21Step4Chunk7_0_checked, root4Node21Step4Chunk7_1_checked, root4Node21Step4Chunk7_2_checked, root4Node21Step4Chunk7_3_checked, root4Node21Step4Chunk7_4_checked, root4Node21Step4Chunk7_5_checked, root4Node21Step4Chunk8_0_checked, root4Node21Step4Chunk8_1_checked, root4Node21Step4Chunk8_2_checked, root4Node21Step4Chunk8_3_checked, root4Node21Step4Chunk8_4_checked, root4Node21Step4Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node21Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node21Domains4 (.output 10) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
