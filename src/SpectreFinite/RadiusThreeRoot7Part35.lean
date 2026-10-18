module

public import SpectreFinite.RadiusThreeRoot7Part34
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable24
public import SpectreFinite.RadiusThreeTable25
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node52Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(6,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node52Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node52Domains4_fast_eq : root7Node52Domains4 = expandDomains root7Node52Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains4 v = expandDomains root7Node52Domains4Fast v from by decide) v
theorem root7Node52Step4Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root7Node52Domains3 root7Node52Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains3 root7Node52Domains4
    root7Node52Domains3Fast root7Node52Domains4Fast
    root7Node52Domains3_fast_eq root7Node52Domains4_fast_eq (by decide)
theorem root7Node52Step4_checked :
    checkReplacement table24 root7Node52Domains3 root7Node52Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step4Chunk0_0_checked, root7Node52Step4Chunk0_1_checked, root7Node52Step4Chunk0_2_checked, root7Node52Step4Chunk0_3_checked, root7Node52Step4Chunk0_4_checked, root7Node52Step4Chunk0_5_checked, root7Node52Step4Chunk1_0_checked, root7Node52Step4Chunk1_1_checked, root7Node52Step4Chunk1_2_checked, root7Node52Step4Chunk1_3_checked, root7Node52Step4Chunk1_4_checked, root7Node52Step4Chunk1_5_checked, root7Node52Step4Chunk2_0_checked, root7Node52Step4Chunk2_1_checked, root7Node52Step4Chunk2_2_checked, root7Node52Step4Chunk2_3_checked, root7Node52Step4Chunk2_4_checked, root7Node52Step4Chunk2_5_checked, root7Node52Step4Chunk3_0_checked, root7Node52Step4Chunk3_1_checked, root7Node52Step4Chunk3_2_checked, root7Node52Step4Chunk3_3_checked, root7Node52Step4Chunk3_4_checked, root7Node52Step4Chunk3_5_checked, root7Node52Step4Chunk4_0_checked, root7Node52Step4Chunk4_1_checked, root7Node52Step4Chunk4_2_checked, root7Node52Step4Chunk4_3_checked, root7Node52Step4Chunk4_4_checked, root7Node52Step4Chunk4_5_checked, root7Node52Step4Chunk5_0_checked, root7Node52Step4Chunk5_1_checked, root7Node52Step4Chunk5_2_checked, root7Node52Step4Chunk5_3_checked, root7Node52Step4Chunk5_4_checked, root7Node52Step4Chunk5_5_checked, root7Node52Step4Chunk6_0_checked, root7Node52Step4Chunk6_1_checked, root7Node52Step4Chunk6_2_checked, root7Node52Step4Chunk6_3_checked, root7Node52Step4Chunk6_4_checked, root7Node52Step4Chunk6_5_checked, root7Node52Step4Chunk7_0_checked, root7Node52Step4Chunk7_1_checked, root7Node52Step4Chunk7_2_checked, root7Node52Step4Chunk7_3_checked, root7Node52Step4Chunk7_4_checked, root7Node52Step4Chunk7_5_checked, root7Node52Step4Chunk8_0_checked, root7Node52Step4Chunk8_1_checked, root7Node52Step4Chunk8_2_checked, root7Node52Step4Chunk8_3_checked, root7Node52Step4Chunk8_4_checked, root7Node52Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node52Domains5 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(6,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(5,3),(7,0)]
def root7Node52Domains5Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(5,3),(7,0)]
theorem root7Node52Domains5_fast_eq : root7Node52Domains5 = expandDomains root7Node52Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains5 v = expandDomains root7Node52Domains5Fast v from by decide) v
theorem root7Node52Step5Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node52Domains4 root7Node52Domains5 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains4 root7Node52Domains5
    root7Node52Domains4Fast root7Node52Domains5Fast
    root7Node52Domains4_fast_eq root7Node52Domains5_fast_eq (by decide)
theorem root7Node52Step5_checked :
    checkReplacement table25 root7Node52Domains4 root7Node52Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step5Chunk0_0_checked, root7Node52Step5Chunk0_1_checked, root7Node52Step5Chunk0_2_checked, root7Node52Step5Chunk0_3_checked, root7Node52Step5Chunk0_4_checked, root7Node52Step5Chunk0_5_checked, root7Node52Step5Chunk1_0_checked, root7Node52Step5Chunk1_1_checked, root7Node52Step5Chunk1_2_checked, root7Node52Step5Chunk1_3_checked, root7Node52Step5Chunk1_4_checked, root7Node52Step5Chunk1_5_checked, root7Node52Step5Chunk2_0_checked, root7Node52Step5Chunk2_1_checked, root7Node52Step5Chunk2_2_checked, root7Node52Step5Chunk2_3_checked, root7Node52Step5Chunk2_4_checked, root7Node52Step5Chunk2_5_checked, root7Node52Step5Chunk3_0_checked, root7Node52Step5Chunk3_1_checked, root7Node52Step5Chunk3_2_checked, root7Node52Step5Chunk3_3_checked, root7Node52Step5Chunk3_4_checked, root7Node52Step5Chunk3_5_checked, root7Node52Step5Chunk4_0_checked, root7Node52Step5Chunk4_1_checked, root7Node52Step5Chunk4_2_checked, root7Node52Step5Chunk4_3_checked, root7Node52Step5Chunk4_4_checked, root7Node52Step5Chunk4_5_checked, root7Node52Step5Chunk5_0_checked, root7Node52Step5Chunk5_1_checked, root7Node52Step5Chunk5_2_checked, root7Node52Step5Chunk5_3_checked, root7Node52Step5Chunk5_4_checked, root7Node52Step5Chunk5_5_checked, root7Node52Step5Chunk6_0_checked, root7Node52Step5Chunk6_1_checked, root7Node52Step5Chunk6_2_checked, root7Node52Step5Chunk6_3_checked, root7Node52Step5Chunk6_4_checked, root7Node52Step5Chunk6_5_checked, root7Node52Step5Chunk7_0_checked, root7Node52Step5Chunk7_1_checked, root7Node52Step5Chunk7_2_checked, root7Node52Step5Chunk7_3_checked, root7Node52Step5Chunk7_4_checked, root7Node52Step5Chunk7_5_checked, root7Node52Step5Chunk8_0_checked, root7Node52Step5Chunk8_1_checked, root7Node52Step5Chunk8_2_checked, root7Node52Step5Chunk8_3_checked, root7Node52Step5Chunk8_4_checked, root7Node52Step5Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node52Domains6 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(6,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(5,3),(7,0)]
def root7Node52Domains6Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(5,3),(7,0)]
theorem root7Node52Domains6_fast_eq : root7Node52Domains6 = expandDomains root7Node52Domains6Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains6 v = expandDomains root7Node52Domains6Fast v from by decide) v
theorem root7Node52Step6Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root7Node52Domains5 root7Node52Domains6 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains5 root7Node52Domains6
    root7Node52Domains5Fast root7Node52Domains6Fast
    root7Node52Domains5_fast_eq root7Node52Domains6_fast_eq (by decide)
theorem root7Node52Step6_checked :
    checkReplacement table30 root7Node52Domains5 root7Node52Domains6 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step6Chunk0_0_checked, root7Node52Step6Chunk0_1_checked, root7Node52Step6Chunk0_2_checked, root7Node52Step6Chunk0_3_checked, root7Node52Step6Chunk0_4_checked, root7Node52Step6Chunk0_5_checked, root7Node52Step6Chunk1_0_checked, root7Node52Step6Chunk1_1_checked, root7Node52Step6Chunk1_2_checked, root7Node52Step6Chunk1_3_checked, root7Node52Step6Chunk1_4_checked, root7Node52Step6Chunk1_5_checked, root7Node52Step6Chunk2_0_checked, root7Node52Step6Chunk2_1_checked, root7Node52Step6Chunk2_2_checked, root7Node52Step6Chunk2_3_checked, root7Node52Step6Chunk2_4_checked, root7Node52Step6Chunk2_5_checked, root7Node52Step6Chunk3_0_checked, root7Node52Step6Chunk3_1_checked, root7Node52Step6Chunk3_2_checked, root7Node52Step6Chunk3_3_checked, root7Node52Step6Chunk3_4_checked, root7Node52Step6Chunk3_5_checked, root7Node52Step6Chunk4_0_checked, root7Node52Step6Chunk4_1_checked, root7Node52Step6Chunk4_2_checked, root7Node52Step6Chunk4_3_checked, root7Node52Step6Chunk4_4_checked, root7Node52Step6Chunk4_5_checked, root7Node52Step6Chunk5_0_checked, root7Node52Step6Chunk5_1_checked, root7Node52Step6Chunk5_2_checked, root7Node52Step6Chunk5_3_checked, root7Node52Step6Chunk5_4_checked, root7Node52Step6Chunk5_5_checked, root7Node52Step6Chunk6_0_checked, root7Node52Step6Chunk6_1_checked, root7Node52Step6Chunk6_2_checked, root7Node52Step6Chunk6_3_checked, root7Node52Step6Chunk6_4_checked, root7Node52Step6Chunk6_5_checked, root7Node52Step6Chunk7_0_checked, root7Node52Step6Chunk7_1_checked, root7Node52Step6Chunk7_2_checked, root7Node52Step6Chunk7_3_checked, root7Node52Step6Chunk7_4_checked, root7Node52Step6Chunk7_5_checked, root7Node52Step6Chunk8_0_checked, root7Node52Step6Chunk8_1_checked, root7Node52Step6Chunk8_2_checked, root7Node52Step6Chunk8_3_checked, root7Node52Step6Chunk8_4_checked, root7Node52Step6Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
