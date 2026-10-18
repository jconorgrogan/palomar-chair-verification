module

public import SpectreFinite.RadiusThreeRoot7Part35
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable9

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node52Domains7 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,1),(6,1)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0)]
  | 16 => [(5,3),(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(7,4)]
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
def root7Node52Domains7Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,1),(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
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
theorem root7Node52Domains7_fast_eq : root7Node52Domains7 = expandDomains root7Node52Domains7Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains7 v = expandDomains root7Node52Domains7Fast v from by decide) v
theorem root7Node52Step7Chunk0_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk0_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk0_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk0_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk0_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk0_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk1_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk1_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk1_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk1_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk1_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk1_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk2_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk2_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk2_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk2_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk2_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk2_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk3_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk3_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk3_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk3_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk3_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk3_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk4_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk4_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk4_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk4_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk4_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk4_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk5_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk5_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk5_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk5_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk5_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk5_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk6_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk6_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk6_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk6_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk6_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk6_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk7_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk7_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk7_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk7_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk7_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk7_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk8_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_0⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk8_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_1⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk8_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_2⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk8_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_3⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk8_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_4⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7Chunk8_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_5⟩
      root7Node52Domains6 root7Node52Domains7 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains6 root7Node52Domains7
    root7Node52Domains6Fast root7Node52Domains7Fast
    root7Node52Domains6_fast_eq root7Node52Domains7_fast_eq (by decide)
theorem root7Node52Step7_checked :
    checkReplacement table9 root7Node52Domains6 root7Node52Domains7 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step7Chunk0_0_checked, root7Node52Step7Chunk0_1_checked, root7Node52Step7Chunk0_2_checked, root7Node52Step7Chunk0_3_checked, root7Node52Step7Chunk0_4_checked, root7Node52Step7Chunk0_5_checked, root7Node52Step7Chunk1_0_checked, root7Node52Step7Chunk1_1_checked, root7Node52Step7Chunk1_2_checked, root7Node52Step7Chunk1_3_checked, root7Node52Step7Chunk1_4_checked, root7Node52Step7Chunk1_5_checked, root7Node52Step7Chunk2_0_checked, root7Node52Step7Chunk2_1_checked, root7Node52Step7Chunk2_2_checked, root7Node52Step7Chunk2_3_checked, root7Node52Step7Chunk2_4_checked, root7Node52Step7Chunk2_5_checked, root7Node52Step7Chunk3_0_checked, root7Node52Step7Chunk3_1_checked, root7Node52Step7Chunk3_2_checked, root7Node52Step7Chunk3_3_checked, root7Node52Step7Chunk3_4_checked, root7Node52Step7Chunk3_5_checked, root7Node52Step7Chunk4_0_checked, root7Node52Step7Chunk4_1_checked, root7Node52Step7Chunk4_2_checked, root7Node52Step7Chunk4_3_checked, root7Node52Step7Chunk4_4_checked, root7Node52Step7Chunk4_5_checked, root7Node52Step7Chunk5_0_checked, root7Node52Step7Chunk5_1_checked, root7Node52Step7Chunk5_2_checked, root7Node52Step7Chunk5_3_checked, root7Node52Step7Chunk5_4_checked, root7Node52Step7Chunk5_5_checked, root7Node52Step7Chunk6_0_checked, root7Node52Step7Chunk6_1_checked, root7Node52Step7Chunk6_2_checked, root7Node52Step7Chunk6_3_checked, root7Node52Step7Chunk6_4_checked, root7Node52Step7Chunk6_5_checked, root7Node52Step7Chunk7_0_checked, root7Node52Step7Chunk7_1_checked, root7Node52Step7Chunk7_2_checked, root7Node52Step7Chunk7_3_checked, root7Node52Step7Chunk7_4_checked, root7Node52Step7Chunk7_5_checked, root7Node52Step7Chunk8_0_checked, root7Node52Step7Chunk8_1_checked, root7Node52Step7Chunk8_2_checked, root7Node52Step7Chunk8_3_checked, root7Node52Step7Chunk8_4_checked, root7Node52Step7Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node53Domains0 : Domains 37 State := restrict root7Node52Domains7 0 (4,2)
def root7Node53Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,1),(6,1)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
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
theorem root7Node53Domains0_fast_eq : root7Node53Domains0 = expandDomains root7Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node53Domains0 v = expandDomains root7Node53Domains0Fast v from by decide) v
def root7Node53Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
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
def root7Node53Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
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
theorem root7Node53Domains1_fast_eq : root7Node53Domains1 = expandDomains root7Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node53Domains1 v = expandDomains root7Node53Domains1Fast v from by decide) v
theorem root7Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root7Node53Domains0 root7Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains0 root7Node53Domains1
    root7Node53Domains0Fast root7Node53Domains1Fast
    root7Node53Domains0_fast_eq root7Node53Domains1_fast_eq (by decide)
theorem root7Node53Step1_checked :
    checkReplacement table11 root7Node53Domains0 root7Node53Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node53Step1Chunk0_0_checked, root7Node53Step1Chunk0_1_checked, root7Node53Step1Chunk0_2_checked, root7Node53Step1Chunk0_3_checked, root7Node53Step1Chunk0_4_checked, root7Node53Step1Chunk0_5_checked, root7Node53Step1Chunk1_0_checked, root7Node53Step1Chunk1_1_checked, root7Node53Step1Chunk1_2_checked, root7Node53Step1Chunk1_3_checked, root7Node53Step1Chunk1_4_checked, root7Node53Step1Chunk1_5_checked, root7Node53Step1Chunk2_0_checked, root7Node53Step1Chunk2_1_checked, root7Node53Step1Chunk2_2_checked, root7Node53Step1Chunk2_3_checked, root7Node53Step1Chunk2_4_checked, root7Node53Step1Chunk2_5_checked, root7Node53Step1Chunk3_0_checked, root7Node53Step1Chunk3_1_checked, root7Node53Step1Chunk3_2_checked, root7Node53Step1Chunk3_3_checked, root7Node53Step1Chunk3_4_checked, root7Node53Step1Chunk3_5_checked, root7Node53Step1Chunk4_0_checked, root7Node53Step1Chunk4_1_checked, root7Node53Step1Chunk4_2_checked, root7Node53Step1Chunk4_3_checked, root7Node53Step1Chunk4_4_checked, root7Node53Step1Chunk4_5_checked, root7Node53Step1Chunk5_0_checked, root7Node53Step1Chunk5_1_checked, root7Node53Step1Chunk5_2_checked, root7Node53Step1Chunk5_3_checked, root7Node53Step1Chunk5_4_checked, root7Node53Step1Chunk5_5_checked, root7Node53Step1Chunk6_0_checked, root7Node53Step1Chunk6_1_checked, root7Node53Step1Chunk6_2_checked, root7Node53Step1Chunk6_3_checked, root7Node53Step1Chunk6_4_checked, root7Node53Step1Chunk6_5_checked, root7Node53Step1Chunk7_0_checked, root7Node53Step1Chunk7_1_checked, root7Node53Step1Chunk7_2_checked, root7Node53Step1Chunk7_3_checked, root7Node53Step1Chunk7_4_checked, root7Node53Step1Chunk7_5_checked, root7Node53Step1Chunk8_0_checked, root7Node53Step1Chunk8_1_checked, root7Node53Step1Chunk8_2_checked, root7Node53Step1Chunk8_3_checked, root7Node53Step1Chunk8_4_checked, root7Node53Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node53Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,4)]
  | 15 => [(4,2),(7,0),(8,0)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(6,1)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node53Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node53Domains2_fast_eq : root7Node53Domains2 = expandDomains root7Node53Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node53Domains2 v = expandDomains root7Node53Domains2Fast v from by decide) v
theorem root7Node53Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node53Domains1 root7Node53Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains1 root7Node53Domains2
    root7Node53Domains1Fast root7Node53Domains2Fast
    root7Node53Domains1_fast_eq root7Node53Domains2_fast_eq (by decide)
theorem root7Node53Step2_checked :
    checkReplacement table26 root7Node53Domains1 root7Node53Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node53Step2Chunk0_0_checked, root7Node53Step2Chunk0_1_checked, root7Node53Step2Chunk0_2_checked, root7Node53Step2Chunk0_3_checked, root7Node53Step2Chunk0_4_checked, root7Node53Step2Chunk0_5_checked, root7Node53Step2Chunk1_0_checked, root7Node53Step2Chunk1_1_checked, root7Node53Step2Chunk1_2_checked, root7Node53Step2Chunk1_3_checked, root7Node53Step2Chunk1_4_checked, root7Node53Step2Chunk1_5_checked, root7Node53Step2Chunk2_0_checked, root7Node53Step2Chunk2_1_checked, root7Node53Step2Chunk2_2_checked, root7Node53Step2Chunk2_3_checked, root7Node53Step2Chunk2_4_checked, root7Node53Step2Chunk2_5_checked, root7Node53Step2Chunk3_0_checked, root7Node53Step2Chunk3_1_checked, root7Node53Step2Chunk3_2_checked, root7Node53Step2Chunk3_3_checked, root7Node53Step2Chunk3_4_checked, root7Node53Step2Chunk3_5_checked, root7Node53Step2Chunk4_0_checked, root7Node53Step2Chunk4_1_checked, root7Node53Step2Chunk4_2_checked, root7Node53Step2Chunk4_3_checked, root7Node53Step2Chunk4_4_checked, root7Node53Step2Chunk4_5_checked, root7Node53Step2Chunk5_0_checked, root7Node53Step2Chunk5_1_checked, root7Node53Step2Chunk5_2_checked, root7Node53Step2Chunk5_3_checked, root7Node53Step2Chunk5_4_checked, root7Node53Step2Chunk5_5_checked, root7Node53Step2Chunk6_0_checked, root7Node53Step2Chunk6_1_checked, root7Node53Step2Chunk6_2_checked, root7Node53Step2Chunk6_3_checked, root7Node53Step2Chunk6_4_checked, root7Node53Step2Chunk6_5_checked, root7Node53Step2Chunk7_0_checked, root7Node53Step2Chunk7_1_checked, root7Node53Step2Chunk7_2_checked, root7Node53Step2Chunk7_3_checked, root7Node53Step2Chunk7_4_checked, root7Node53Step2Chunk7_5_checked, root7Node53Step2Chunk8_0_checked, root7Node53Step2Chunk8_1_checked, root7Node53Step2Chunk8_2_checked, root7Node53Step2Chunk8_3_checked, root7Node53Step2Chunk8_4_checked, root7Node53Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
