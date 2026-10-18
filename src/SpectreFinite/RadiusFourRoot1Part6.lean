module

public import SpectreFinite.RadiusFourRoot1Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node14Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root1Node14Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node14Domains2_fast_eq : root1Node14Domains2 = expandDomains root1Node14Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node14Domains2 v = expandDomains root1Node14Domains2Fast v from by decide) v
theorem root1Node14Step2Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root1Node14Domains1 root1Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains1 root1Node14Domains2
    root1Node14Domains1Fast root1Node14Domains2Fast
    root1Node14Domains1_fast_eq root1Node14Domains2_fast_eq (by decide)
theorem root1Node14Step2_checked :
    checkReplacement table37 root1Node14Domains1 root1Node14Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node14Step2Chunk0_0_checked, root1Node14Step2Chunk0_1_checked, root1Node14Step2Chunk0_2_checked, root1Node14Step2Chunk0_3_checked, root1Node14Step2Chunk0_4_checked, root1Node14Step2Chunk0_5_checked, root1Node14Step2Chunk1_0_checked, root1Node14Step2Chunk1_1_checked, root1Node14Step2Chunk1_2_checked, root1Node14Step2Chunk1_3_checked, root1Node14Step2Chunk1_4_checked, root1Node14Step2Chunk1_5_checked, root1Node14Step2Chunk2_0_checked, root1Node14Step2Chunk2_1_checked, root1Node14Step2Chunk2_2_checked, root1Node14Step2Chunk2_3_checked, root1Node14Step2Chunk2_4_checked, root1Node14Step2Chunk2_5_checked, root1Node14Step2Chunk3_0_checked, root1Node14Step2Chunk3_1_checked, root1Node14Step2Chunk3_2_checked, root1Node14Step2Chunk3_3_checked, root1Node14Step2Chunk3_4_checked, root1Node14Step2Chunk3_5_checked, root1Node14Step2Chunk4_0_checked, root1Node14Step2Chunk4_1_checked, root1Node14Step2Chunk4_2_checked, root1Node14Step2Chunk4_3_checked, root1Node14Step2Chunk4_4_checked, root1Node14Step2Chunk4_5_checked, root1Node14Step2Chunk5_0_checked, root1Node14Step2Chunk5_1_checked, root1Node14Step2Chunk5_2_checked, root1Node14Step2Chunk5_3_checked, root1Node14Step2Chunk5_4_checked, root1Node14Step2Chunk5_5_checked, root1Node14Step2Chunk6_0_checked, root1Node14Step2Chunk6_1_checked, root1Node14Step2Chunk6_2_checked, root1Node14Step2Chunk6_3_checked, root1Node14Step2Chunk6_4_checked, root1Node14Step2Chunk6_5_checked, root1Node14Step2Chunk7_0_checked, root1Node14Step2Chunk7_1_checked, root1Node14Step2Chunk7_2_checked, root1Node14Step2Chunk7_3_checked, root1Node14Step2Chunk7_4_checked, root1Node14Step2Chunk7_5_checked, root1Node14Step2Chunk8_0_checked, root1Node14Step2Chunk8_1_checked, root1Node14Step2Chunk8_2_checked, root1Node14Step2Chunk8_3_checked, root1Node14Step2Chunk8_4_checked, root1Node14Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node15Domains0 : Domains 61 State := restrict root1Node14Domains2 35 (1,2)
def root1Node15Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node15Domains0_fast_eq : root1Node15Domains0 = expandDomains root1Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node15Domains0 v = expandDomains root1Node15Domains0Fast v from by decide) v
def root1Node15Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root1Node15Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node15Domains1_fast_eq : root1Node15Domains1 = expandDomains root1Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node15Domains1 v = expandDomains root1Node15Domains1Fast v from by decide) v
theorem root1Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node15Domains0 root1Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node15Domains0 root1Node15Domains1
    root1Node15Domains0Fast root1Node15Domains1Fast
    root1Node15Domains0_fast_eq root1Node15Domains1_fast_eq (by decide)
theorem root1Node15Step1_checked :
    checkReplacement table26 root1Node15Domains0 root1Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node15Step1Chunk0_0_checked, root1Node15Step1Chunk0_1_checked, root1Node15Step1Chunk0_2_checked, root1Node15Step1Chunk0_3_checked, root1Node15Step1Chunk0_4_checked, root1Node15Step1Chunk0_5_checked, root1Node15Step1Chunk1_0_checked, root1Node15Step1Chunk1_1_checked, root1Node15Step1Chunk1_2_checked, root1Node15Step1Chunk1_3_checked, root1Node15Step1Chunk1_4_checked, root1Node15Step1Chunk1_5_checked, root1Node15Step1Chunk2_0_checked, root1Node15Step1Chunk2_1_checked, root1Node15Step1Chunk2_2_checked, root1Node15Step1Chunk2_3_checked, root1Node15Step1Chunk2_4_checked, root1Node15Step1Chunk2_5_checked, root1Node15Step1Chunk3_0_checked, root1Node15Step1Chunk3_1_checked, root1Node15Step1Chunk3_2_checked, root1Node15Step1Chunk3_3_checked, root1Node15Step1Chunk3_4_checked, root1Node15Step1Chunk3_5_checked, root1Node15Step1Chunk4_0_checked, root1Node15Step1Chunk4_1_checked, root1Node15Step1Chunk4_2_checked, root1Node15Step1Chunk4_3_checked, root1Node15Step1Chunk4_4_checked, root1Node15Step1Chunk4_5_checked, root1Node15Step1Chunk5_0_checked, root1Node15Step1Chunk5_1_checked, root1Node15Step1Chunk5_2_checked, root1Node15Step1Chunk5_3_checked, root1Node15Step1Chunk5_4_checked, root1Node15Step1Chunk5_5_checked, root1Node15Step1Chunk6_0_checked, root1Node15Step1Chunk6_1_checked, root1Node15Step1Chunk6_2_checked, root1Node15Step1Chunk6_3_checked, root1Node15Step1Chunk6_4_checked, root1Node15Step1Chunk6_5_checked, root1Node15Step1Chunk7_0_checked, root1Node15Step1Chunk7_1_checked, root1Node15Step1Chunk7_2_checked, root1Node15Step1Chunk7_3_checked, root1Node15Step1Chunk7_4_checked, root1Node15Step1Chunk7_5_checked, root1Node15Step1Chunk8_0_checked, root1Node15Step1Chunk8_1_checked, root1Node15Step1Chunk8_2_checked, root1Node15Step1Chunk8_3_checked, root1Node15Step1Chunk8_4_checked, root1Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node16Domains0 : Domains 61 State := restrict root1Node15Domains1 42 (5,0)
def root1Node16Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node16Domains0_fast_eq : root1Node16Domains0 = expandDomains root1Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node16Domains0 v = expandDomains root1Node16Domains0Fast v from by decide) v
def root1Node16Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3)]
  | 59 => [(8,2)]
  | _ => [(5,0)]
def root1Node16Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(5,0)]
theorem root1Node16Domains1_fast_eq : root1Node16Domains1 = expandDomains root1Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node16Domains1 v = expandDomains root1Node16Domains1Fast v from by decide) v
theorem root1Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node16Domains0 root1Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node16Domains0 root1Node16Domains1
    root1Node16Domains0Fast root1Node16Domains1Fast
    root1Node16Domains0_fast_eq root1Node16Domains1_fast_eq (by decide)
theorem root1Node16Step1_checked :
    checkReplacement table39 root1Node16Domains0 root1Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node16Step1Chunk0_0_checked, root1Node16Step1Chunk0_1_checked, root1Node16Step1Chunk0_2_checked, root1Node16Step1Chunk0_3_checked, root1Node16Step1Chunk0_4_checked, root1Node16Step1Chunk0_5_checked, root1Node16Step1Chunk1_0_checked, root1Node16Step1Chunk1_1_checked, root1Node16Step1Chunk1_2_checked, root1Node16Step1Chunk1_3_checked, root1Node16Step1Chunk1_4_checked, root1Node16Step1Chunk1_5_checked, root1Node16Step1Chunk2_0_checked, root1Node16Step1Chunk2_1_checked, root1Node16Step1Chunk2_2_checked, root1Node16Step1Chunk2_3_checked, root1Node16Step1Chunk2_4_checked, root1Node16Step1Chunk2_5_checked, root1Node16Step1Chunk3_0_checked, root1Node16Step1Chunk3_1_checked, root1Node16Step1Chunk3_2_checked, root1Node16Step1Chunk3_3_checked, root1Node16Step1Chunk3_4_checked, root1Node16Step1Chunk3_5_checked, root1Node16Step1Chunk4_0_checked, root1Node16Step1Chunk4_1_checked, root1Node16Step1Chunk4_2_checked, root1Node16Step1Chunk4_3_checked, root1Node16Step1Chunk4_4_checked, root1Node16Step1Chunk4_5_checked, root1Node16Step1Chunk5_0_checked, root1Node16Step1Chunk5_1_checked, root1Node16Step1Chunk5_2_checked, root1Node16Step1Chunk5_3_checked, root1Node16Step1Chunk5_4_checked, root1Node16Step1Chunk5_5_checked, root1Node16Step1Chunk6_0_checked, root1Node16Step1Chunk6_1_checked, root1Node16Step1Chunk6_2_checked, root1Node16Step1Chunk6_3_checked, root1Node16Step1Chunk6_4_checked, root1Node16Step1Chunk6_5_checked, root1Node16Step1Chunk7_0_checked, root1Node16Step1Chunk7_1_checked, root1Node16Step1Chunk7_2_checked, root1Node16Step1Chunk7_3_checked, root1Node16Step1Chunk7_4_checked, root1Node16Step1Chunk7_5_checked, root1Node16Step1Chunk8_0_checked, root1Node16Step1Chunk8_1_checked, root1Node16Step1Chunk8_2_checked, root1Node16Step1Chunk8_3_checked, root1Node16Step1Chunk8_4_checked, root1Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node16Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node16Domains1 (.output 6) = true := by decide
def root1Node17Domains0 : Domains 61 State := restrict root1Node15Domains1 42 (8,0)
def root1Node17Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node17Domains0_fast_eq : root1Node17Domains0 = expandDomains root1Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node17Domains0 v = expandDomains root1Node17Domains0Fast v from by decide) v
def root1Node17Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(8,0)]
def root1Node17Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root1Node17Domains1_fast_eq : root1Node17Domains1 = expandDomains root1Node17Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node17Domains1 v = expandDomains root1Node17Domains1Fast v from by decide) v
theorem root1Node17Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node17Domains0 root1Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node17Domains0 root1Node17Domains1
    root1Node17Domains0Fast root1Node17Domains1Fast
    root1Node17Domains0_fast_eq root1Node17Domains1_fast_eq (by decide)
theorem root1Node17Step1_checked :
    checkReplacement table39 root1Node17Domains0 root1Node17Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node17Step1Chunk0_0_checked, root1Node17Step1Chunk0_1_checked, root1Node17Step1Chunk0_2_checked, root1Node17Step1Chunk0_3_checked, root1Node17Step1Chunk0_4_checked, root1Node17Step1Chunk0_5_checked, root1Node17Step1Chunk1_0_checked, root1Node17Step1Chunk1_1_checked, root1Node17Step1Chunk1_2_checked, root1Node17Step1Chunk1_3_checked, root1Node17Step1Chunk1_4_checked, root1Node17Step1Chunk1_5_checked, root1Node17Step1Chunk2_0_checked, root1Node17Step1Chunk2_1_checked, root1Node17Step1Chunk2_2_checked, root1Node17Step1Chunk2_3_checked, root1Node17Step1Chunk2_4_checked, root1Node17Step1Chunk2_5_checked, root1Node17Step1Chunk3_0_checked, root1Node17Step1Chunk3_1_checked, root1Node17Step1Chunk3_2_checked, root1Node17Step1Chunk3_3_checked, root1Node17Step1Chunk3_4_checked, root1Node17Step1Chunk3_5_checked, root1Node17Step1Chunk4_0_checked, root1Node17Step1Chunk4_1_checked, root1Node17Step1Chunk4_2_checked, root1Node17Step1Chunk4_3_checked, root1Node17Step1Chunk4_4_checked, root1Node17Step1Chunk4_5_checked, root1Node17Step1Chunk5_0_checked, root1Node17Step1Chunk5_1_checked, root1Node17Step1Chunk5_2_checked, root1Node17Step1Chunk5_3_checked, root1Node17Step1Chunk5_4_checked, root1Node17Step1Chunk5_5_checked, root1Node17Step1Chunk6_0_checked, root1Node17Step1Chunk6_1_checked, root1Node17Step1Chunk6_2_checked, root1Node17Step1Chunk6_3_checked, root1Node17Step1Chunk6_4_checked, root1Node17Step1Chunk6_5_checked, root1Node17Step1Chunk7_0_checked, root1Node17Step1Chunk7_1_checked, root1Node17Step1Chunk7_2_checked, root1Node17Step1Chunk7_3_checked, root1Node17Step1Chunk7_4_checked, root1Node17Step1Chunk7_5_checked, root1Node17Step1Chunk8_0_checked, root1Node17Step1Chunk8_1_checked, root1Node17Step1Chunk8_2_checked, root1Node17Step1Chunk8_3_checked, root1Node17Step1Chunk8_4_checked, root1Node17Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node18Domains0 : Domains 61 State := restrict root1Node17Domains1 58 (1,3)
def root1Node18Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root1Node18Domains0_fast_eq : root1Node18Domains0 = expandDomains root1Node18Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node18Domains0 v = expandDomains root1Node18Domains0Fast v from by decide) v
def root1Node18Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3)]
  | 59 => [(8,2)]
  | _ => [(8,0)]
def root1Node18Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(8,0)]
theorem root1Node18Domains1_fast_eq : root1Node18Domains1 = expandDomains root1Node18Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node18Domains1 v = expandDomains root1Node18Domains1Fast v from by decide) v
theorem root1Node18Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node18Domains0 root1Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node18Domains0 root1Node18Domains1
    root1Node18Domains0Fast root1Node18Domains1Fast
    root1Node18Domains0_fast_eq root1Node18Domains1_fast_eq (by decide)
theorem root1Node18Step1_checked :
    checkReplacement table39 root1Node18Domains0 root1Node18Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node18Step1Chunk0_0_checked, root1Node18Step1Chunk0_1_checked, root1Node18Step1Chunk0_2_checked, root1Node18Step1Chunk0_3_checked, root1Node18Step1Chunk0_4_checked, root1Node18Step1Chunk0_5_checked, root1Node18Step1Chunk1_0_checked, root1Node18Step1Chunk1_1_checked, root1Node18Step1Chunk1_2_checked, root1Node18Step1Chunk1_3_checked, root1Node18Step1Chunk1_4_checked, root1Node18Step1Chunk1_5_checked, root1Node18Step1Chunk2_0_checked, root1Node18Step1Chunk2_1_checked, root1Node18Step1Chunk2_2_checked, root1Node18Step1Chunk2_3_checked, root1Node18Step1Chunk2_4_checked, root1Node18Step1Chunk2_5_checked, root1Node18Step1Chunk3_0_checked, root1Node18Step1Chunk3_1_checked, root1Node18Step1Chunk3_2_checked, root1Node18Step1Chunk3_3_checked, root1Node18Step1Chunk3_4_checked, root1Node18Step1Chunk3_5_checked, root1Node18Step1Chunk4_0_checked, root1Node18Step1Chunk4_1_checked, root1Node18Step1Chunk4_2_checked, root1Node18Step1Chunk4_3_checked, root1Node18Step1Chunk4_4_checked, root1Node18Step1Chunk4_5_checked, root1Node18Step1Chunk5_0_checked, root1Node18Step1Chunk5_1_checked, root1Node18Step1Chunk5_2_checked, root1Node18Step1Chunk5_3_checked, root1Node18Step1Chunk5_4_checked, root1Node18Step1Chunk5_5_checked, root1Node18Step1Chunk6_0_checked, root1Node18Step1Chunk6_1_checked, root1Node18Step1Chunk6_2_checked, root1Node18Step1Chunk6_3_checked, root1Node18Step1Chunk6_4_checked, root1Node18Step1Chunk6_5_checked, root1Node18Step1Chunk7_0_checked, root1Node18Step1Chunk7_1_checked, root1Node18Step1Chunk7_2_checked, root1Node18Step1Chunk7_3_checked, root1Node18Step1Chunk7_4_checked, root1Node18Step1Chunk7_5_checked, root1Node18Step1Chunk8_0_checked, root1Node18Step1Chunk8_1_checked, root1Node18Step1Chunk8_2_checked, root1Node18Step1Chunk8_3_checked, root1Node18Step1Chunk8_4_checked, root1Node18Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node18Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node18Domains1 (.output 7) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
