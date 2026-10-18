module

public import SpectreFinite.RadiusFourRoot6Part11
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node39Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1),(5,4)]
  | 44 => [(0,1),(6,4)]
  | 45 => [(1,2),(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(7,5),(8,5)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(4,2),(8,2)]
  | 57 => [(5,0),(5,3)]
  | 58 => [(4,5),(5,5),(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node39Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node39Domains2_fast_eq : root6Node39Domains2 = expandDomains root6Node39Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node39Domains2 v = expandDomains root6Node39Domains2Fast v from by decide) v
theorem root6Node39Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root6Node39Domains1 root6Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node39Domains1 root6Node39Domains2
    root6Node39Domains1Fast root6Node39Domains2Fast
    root6Node39Domains1_fast_eq root6Node39Domains2_fast_eq (by decide)
theorem root6Node39Step2_checked :
    checkReplacement table39 root6Node39Domains1 root6Node39Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node39Step2Chunk0_0_checked, root6Node39Step2Chunk0_1_checked, root6Node39Step2Chunk0_2_checked, root6Node39Step2Chunk0_3_checked, root6Node39Step2Chunk0_4_checked, root6Node39Step2Chunk0_5_checked, root6Node39Step2Chunk1_0_checked, root6Node39Step2Chunk1_1_checked, root6Node39Step2Chunk1_2_checked, root6Node39Step2Chunk1_3_checked, root6Node39Step2Chunk1_4_checked, root6Node39Step2Chunk1_5_checked, root6Node39Step2Chunk2_0_checked, root6Node39Step2Chunk2_1_checked, root6Node39Step2Chunk2_2_checked, root6Node39Step2Chunk2_3_checked, root6Node39Step2Chunk2_4_checked, root6Node39Step2Chunk2_5_checked, root6Node39Step2Chunk3_0_checked, root6Node39Step2Chunk3_1_checked, root6Node39Step2Chunk3_2_checked, root6Node39Step2Chunk3_3_checked, root6Node39Step2Chunk3_4_checked, root6Node39Step2Chunk3_5_checked, root6Node39Step2Chunk4_0_checked, root6Node39Step2Chunk4_1_checked, root6Node39Step2Chunk4_2_checked, root6Node39Step2Chunk4_3_checked, root6Node39Step2Chunk4_4_checked, root6Node39Step2Chunk4_5_checked, root6Node39Step2Chunk5_0_checked, root6Node39Step2Chunk5_1_checked, root6Node39Step2Chunk5_2_checked, root6Node39Step2Chunk5_3_checked, root6Node39Step2Chunk5_4_checked, root6Node39Step2Chunk5_5_checked, root6Node39Step2Chunk6_0_checked, root6Node39Step2Chunk6_1_checked, root6Node39Step2Chunk6_2_checked, root6Node39Step2Chunk6_3_checked, root6Node39Step2Chunk6_4_checked, root6Node39Step2Chunk6_5_checked, root6Node39Step2Chunk7_0_checked, root6Node39Step2Chunk7_1_checked, root6Node39Step2Chunk7_2_checked, root6Node39Step2Chunk7_3_checked, root6Node39Step2Chunk7_4_checked, root6Node39Step2Chunk7_5_checked, root6Node39Step2Chunk8_0_checked, root6Node39Step2Chunk8_1_checked, root6Node39Step2Chunk8_2_checked, root6Node39Step2Chunk8_3_checked, root6Node39Step2Chunk8_4_checked, root6Node39Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node40Domains0 : Domains 61 State := restrict root6Node39Domains2 11 (3,3)
def root6Node40Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node40Domains0_fast_eq : root6Node40Domains0 = expandDomains root6Node40Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node40Domains0 v = expandDomains root6Node40Domains0Fast v from by decide) v
def root6Node40Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node40Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node40Domains1_fast_eq : root6Node40Domains1 = expandDomains root6Node40Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node40Domains1 v = expandDomains root6Node40Domains1Fast v from by decide) v
theorem root6Node40Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node40Domains0 root6Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node40Domains0 root6Node40Domains1
    root6Node40Domains0Fast root6Node40Domains1Fast
    root6Node40Domains0_fast_eq root6Node40Domains1_fast_eq (by decide)
theorem root6Node40Step1_checked :
    checkReplacement table37 root6Node40Domains0 root6Node40Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node40Step1Chunk0_0_checked, root6Node40Step1Chunk0_1_checked, root6Node40Step1Chunk0_2_checked, root6Node40Step1Chunk0_3_checked, root6Node40Step1Chunk0_4_checked, root6Node40Step1Chunk0_5_checked, root6Node40Step1Chunk1_0_checked, root6Node40Step1Chunk1_1_checked, root6Node40Step1Chunk1_2_checked, root6Node40Step1Chunk1_3_checked, root6Node40Step1Chunk1_4_checked, root6Node40Step1Chunk1_5_checked, root6Node40Step1Chunk2_0_checked, root6Node40Step1Chunk2_1_checked, root6Node40Step1Chunk2_2_checked, root6Node40Step1Chunk2_3_checked, root6Node40Step1Chunk2_4_checked, root6Node40Step1Chunk2_5_checked, root6Node40Step1Chunk3_0_checked, root6Node40Step1Chunk3_1_checked, root6Node40Step1Chunk3_2_checked, root6Node40Step1Chunk3_3_checked, root6Node40Step1Chunk3_4_checked, root6Node40Step1Chunk3_5_checked, root6Node40Step1Chunk4_0_checked, root6Node40Step1Chunk4_1_checked, root6Node40Step1Chunk4_2_checked, root6Node40Step1Chunk4_3_checked, root6Node40Step1Chunk4_4_checked, root6Node40Step1Chunk4_5_checked, root6Node40Step1Chunk5_0_checked, root6Node40Step1Chunk5_1_checked, root6Node40Step1Chunk5_2_checked, root6Node40Step1Chunk5_3_checked, root6Node40Step1Chunk5_4_checked, root6Node40Step1Chunk5_5_checked, root6Node40Step1Chunk6_0_checked, root6Node40Step1Chunk6_1_checked, root6Node40Step1Chunk6_2_checked, root6Node40Step1Chunk6_3_checked, root6Node40Step1Chunk6_4_checked, root6Node40Step1Chunk6_5_checked, root6Node40Step1Chunk7_0_checked, root6Node40Step1Chunk7_1_checked, root6Node40Step1Chunk7_2_checked, root6Node40Step1Chunk7_3_checked, root6Node40Step1Chunk7_4_checked, root6Node40Step1Chunk7_5_checked, root6Node40Step1Chunk8_0_checked, root6Node40Step1Chunk8_1_checked, root6Node40Step1Chunk8_2_checked, root6Node40Step1Chunk8_3_checked, root6Node40Step1Chunk8_4_checked, root6Node40Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node40Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node40Domains1 (.output 18) = true := by decide
def root6Node41Domains0 : Domains 61 State := restrict root6Node39Domains2 11 (7,3)
def root6Node41Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node41Domains0_fast_eq : root6Node41Domains0 = expandDomains root6Node41Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node41Domains0 v = expandDomains root6Node41Domains0Fast v from by decide) v
def root6Node42Domains0 : Domains 61 State := restrict root6Node41Domains0 26 (4,5)
def root6Node42Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node42Domains0_fast_eq : root6Node42Domains0 = expandDomains root6Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node42Domains0 v = expandDomains root6Node42Domains0Fast v from by decide) v
def root6Node42Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node42Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node42Domains1_fast_eq : root6Node42Domains1 = expandDomains root6Node42Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node42Domains1 v = expandDomains root6Node42Domains1Fast v from by decide) v
theorem root6Node42Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node42Domains0 root6Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node42Domains0 root6Node42Domains1
    root6Node42Domains0Fast root6Node42Domains1Fast
    root6Node42Domains0_fast_eq root6Node42Domains1_fast_eq (by decide)
theorem root6Node42Step1_checked :
    checkReplacement table37 root6Node42Domains0 root6Node42Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node42Step1Chunk0_0_checked, root6Node42Step1Chunk0_1_checked, root6Node42Step1Chunk0_2_checked, root6Node42Step1Chunk0_3_checked, root6Node42Step1Chunk0_4_checked, root6Node42Step1Chunk0_5_checked, root6Node42Step1Chunk1_0_checked, root6Node42Step1Chunk1_1_checked, root6Node42Step1Chunk1_2_checked, root6Node42Step1Chunk1_3_checked, root6Node42Step1Chunk1_4_checked, root6Node42Step1Chunk1_5_checked, root6Node42Step1Chunk2_0_checked, root6Node42Step1Chunk2_1_checked, root6Node42Step1Chunk2_2_checked, root6Node42Step1Chunk2_3_checked, root6Node42Step1Chunk2_4_checked, root6Node42Step1Chunk2_5_checked, root6Node42Step1Chunk3_0_checked, root6Node42Step1Chunk3_1_checked, root6Node42Step1Chunk3_2_checked, root6Node42Step1Chunk3_3_checked, root6Node42Step1Chunk3_4_checked, root6Node42Step1Chunk3_5_checked, root6Node42Step1Chunk4_0_checked, root6Node42Step1Chunk4_1_checked, root6Node42Step1Chunk4_2_checked, root6Node42Step1Chunk4_3_checked, root6Node42Step1Chunk4_4_checked, root6Node42Step1Chunk4_5_checked, root6Node42Step1Chunk5_0_checked, root6Node42Step1Chunk5_1_checked, root6Node42Step1Chunk5_2_checked, root6Node42Step1Chunk5_3_checked, root6Node42Step1Chunk5_4_checked, root6Node42Step1Chunk5_5_checked, root6Node42Step1Chunk6_0_checked, root6Node42Step1Chunk6_1_checked, root6Node42Step1Chunk6_2_checked, root6Node42Step1Chunk6_3_checked, root6Node42Step1Chunk6_4_checked, root6Node42Step1Chunk6_5_checked, root6Node42Step1Chunk7_0_checked, root6Node42Step1Chunk7_1_checked, root6Node42Step1Chunk7_2_checked, root6Node42Step1Chunk7_3_checked, root6Node42Step1Chunk7_4_checked, root6Node42Step1Chunk7_5_checked, root6Node42Step1Chunk8_0_checked, root6Node42Step1Chunk8_1_checked, root6Node42Step1Chunk8_2_checked, root6Node42Step1Chunk8_3_checked, root6Node42Step1Chunk8_4_checked, root6Node42Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node42Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node42Domains1 (.output 19) = true := by decide
def root6Node43Domains0 : Domains 61 State := restrict root6Node41Domains0 26 (8,5)
def root6Node43Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(8,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1),(5,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node43Domains0_fast_eq : root6Node43Domains0 = expandDomains root6Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node43Domains0 v = expandDomains root6Node43Domains0Fast v from by decide) v
def root6Node43Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(8,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(8,2)]
  | 36 => [(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,4)]
  | 44 => [(6,4)]
  | 45 => [(1,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(7,5)]
  | 51 => [(0,3)]
  | 52 => [(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(4,2)]
  | 57 => [(5,3)]
  | 58 => [(5,5),(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node43Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(8,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(8,2)]
  | 36 => some [(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,4)]
  | 44 => some [(6,4)]
  | 45 => some [(1,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(7,5)]
  | 51 => some [(0,3)]
  | 52 => some [(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(4,2)]
  | 57 => some [(5,3)]
  | 58 => some [(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node43Domains1_fast_eq : root6Node43Domains1 = expandDomains root6Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node43Domains1 v = expandDomains root6Node43Domains1Fast v from by decide) v
theorem root6Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node43Domains0 root6Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node43Domains0 root6Node43Domains1
    root6Node43Domains0Fast root6Node43Domains1Fast
    root6Node43Domains0_fast_eq root6Node43Domains1_fast_eq (by decide)
theorem root6Node43Step1_checked :
    checkReplacement table37 root6Node43Domains0 root6Node43Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node43Step1Chunk0_0_checked, root6Node43Step1Chunk0_1_checked, root6Node43Step1Chunk0_2_checked, root6Node43Step1Chunk0_3_checked, root6Node43Step1Chunk0_4_checked, root6Node43Step1Chunk0_5_checked, root6Node43Step1Chunk1_0_checked, root6Node43Step1Chunk1_1_checked, root6Node43Step1Chunk1_2_checked, root6Node43Step1Chunk1_3_checked, root6Node43Step1Chunk1_4_checked, root6Node43Step1Chunk1_5_checked, root6Node43Step1Chunk2_0_checked, root6Node43Step1Chunk2_1_checked, root6Node43Step1Chunk2_2_checked, root6Node43Step1Chunk2_3_checked, root6Node43Step1Chunk2_4_checked, root6Node43Step1Chunk2_5_checked, root6Node43Step1Chunk3_0_checked, root6Node43Step1Chunk3_1_checked, root6Node43Step1Chunk3_2_checked, root6Node43Step1Chunk3_3_checked, root6Node43Step1Chunk3_4_checked, root6Node43Step1Chunk3_5_checked, root6Node43Step1Chunk4_0_checked, root6Node43Step1Chunk4_1_checked, root6Node43Step1Chunk4_2_checked, root6Node43Step1Chunk4_3_checked, root6Node43Step1Chunk4_4_checked, root6Node43Step1Chunk4_5_checked, root6Node43Step1Chunk5_0_checked, root6Node43Step1Chunk5_1_checked, root6Node43Step1Chunk5_2_checked, root6Node43Step1Chunk5_3_checked, root6Node43Step1Chunk5_4_checked, root6Node43Step1Chunk5_5_checked, root6Node43Step1Chunk6_0_checked, root6Node43Step1Chunk6_1_checked, root6Node43Step1Chunk6_2_checked, root6Node43Step1Chunk6_3_checked, root6Node43Step1Chunk6_4_checked, root6Node43Step1Chunk6_5_checked, root6Node43Step1Chunk7_0_checked, root6Node43Step1Chunk7_1_checked, root6Node43Step1Chunk7_2_checked, root6Node43Step1Chunk7_3_checked, root6Node43Step1Chunk7_4_checked, root6Node43Step1Chunk7_5_checked, root6Node43Step1Chunk8_0_checked, root6Node43Step1Chunk8_1_checked, root6Node43Step1Chunk8_2_checked, root6Node43Step1Chunk8_3_checked, root6Node43Step1Chunk8_4_checked, root6Node43Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
