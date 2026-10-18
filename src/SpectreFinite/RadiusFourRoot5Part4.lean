module

public import SpectreFinite.RadiusFourRoot5Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node10Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node10Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node10Domains2_fast_eq : root5Node10Domains2 = expandDomains root5Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node10Domains2 v = expandDomains root5Node10Domains2Fast v from by decide) v
theorem root5Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node10Domains1 root5Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node10Domains1 root5Node10Domains2
    root5Node10Domains1Fast root5Node10Domains2Fast
    root5Node10Domains1_fast_eq root5Node10Domains2_fast_eq (by decide)
theorem root5Node10Step2_checked :
    checkReplacement table4 root5Node10Domains1 root5Node10Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node10Step2Chunk0_0_checked, root5Node10Step2Chunk0_1_checked, root5Node10Step2Chunk0_2_checked, root5Node10Step2Chunk0_3_checked, root5Node10Step2Chunk0_4_checked, root5Node10Step2Chunk0_5_checked, root5Node10Step2Chunk1_0_checked, root5Node10Step2Chunk1_1_checked, root5Node10Step2Chunk1_2_checked, root5Node10Step2Chunk1_3_checked, root5Node10Step2Chunk1_4_checked, root5Node10Step2Chunk1_5_checked, root5Node10Step2Chunk2_0_checked, root5Node10Step2Chunk2_1_checked, root5Node10Step2Chunk2_2_checked, root5Node10Step2Chunk2_3_checked, root5Node10Step2Chunk2_4_checked, root5Node10Step2Chunk2_5_checked, root5Node10Step2Chunk3_0_checked, root5Node10Step2Chunk3_1_checked, root5Node10Step2Chunk3_2_checked, root5Node10Step2Chunk3_3_checked, root5Node10Step2Chunk3_4_checked, root5Node10Step2Chunk3_5_checked, root5Node10Step2Chunk4_0_checked, root5Node10Step2Chunk4_1_checked, root5Node10Step2Chunk4_2_checked, root5Node10Step2Chunk4_3_checked, root5Node10Step2Chunk4_4_checked, root5Node10Step2Chunk4_5_checked, root5Node10Step2Chunk5_0_checked, root5Node10Step2Chunk5_1_checked, root5Node10Step2Chunk5_2_checked, root5Node10Step2Chunk5_3_checked, root5Node10Step2Chunk5_4_checked, root5Node10Step2Chunk5_5_checked, root5Node10Step2Chunk6_0_checked, root5Node10Step2Chunk6_1_checked, root5Node10Step2Chunk6_2_checked, root5Node10Step2Chunk6_3_checked, root5Node10Step2Chunk6_4_checked, root5Node10Step2Chunk6_5_checked, root5Node10Step2Chunk7_0_checked, root5Node10Step2Chunk7_1_checked, root5Node10Step2Chunk7_2_checked, root5Node10Step2Chunk7_3_checked, root5Node10Step2Chunk7_4_checked, root5Node10Step2Chunk7_5_checked, root5Node10Step2Chunk8_0_checked, root5Node10Step2Chunk8_1_checked, root5Node10Step2Chunk8_2_checked, root5Node10Step2Chunk8_3_checked, root5Node10Step2Chunk8_4_checked, root5Node10Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node10Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node10Domains2 (.output 4) = true := by decide
def root5Node11Domains0 : Domains 61 State := restrict root5Node9Domains2 0 (6,0)
def root5Node11Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(3,1),(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node11Domains0_fast_eq : root5Node11Domains0 = expandDomains root5Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node11Domains0 v = expandDomains root5Node11Domains0Fast v from by decide) v
def root5Node12Domains0 : Domains 61 State := restrict root5Node11Domains0 4 (3,1)
def root5Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(3,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node12Domains0_fast_eq : root5Node12Domains0 = expandDomains root5Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node12Domains0 v = expandDomains root5Node12Domains0Fast v from by decide) v
def root5Node12Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(3,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node12Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(3,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node12Domains1_fast_eq : root5Node12Domains1 = expandDomains root5Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node12Domains1 v = expandDomains root5Node12Domains1Fast v from by decide) v
theorem root5Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node12Domains0 root5Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains0 root5Node12Domains1
    root5Node12Domains0Fast root5Node12Domains1Fast
    root5Node12Domains0_fast_eq root5Node12Domains1_fast_eq (by decide)
theorem root5Node12Step1_checked :
    checkReplacement table4 root5Node12Domains0 root5Node12Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node12Step1Chunk0_0_checked, root5Node12Step1Chunk0_1_checked, root5Node12Step1Chunk0_2_checked, root5Node12Step1Chunk0_3_checked, root5Node12Step1Chunk0_4_checked, root5Node12Step1Chunk0_5_checked, root5Node12Step1Chunk1_0_checked, root5Node12Step1Chunk1_1_checked, root5Node12Step1Chunk1_2_checked, root5Node12Step1Chunk1_3_checked, root5Node12Step1Chunk1_4_checked, root5Node12Step1Chunk1_5_checked, root5Node12Step1Chunk2_0_checked, root5Node12Step1Chunk2_1_checked, root5Node12Step1Chunk2_2_checked, root5Node12Step1Chunk2_3_checked, root5Node12Step1Chunk2_4_checked, root5Node12Step1Chunk2_5_checked, root5Node12Step1Chunk3_0_checked, root5Node12Step1Chunk3_1_checked, root5Node12Step1Chunk3_2_checked, root5Node12Step1Chunk3_3_checked, root5Node12Step1Chunk3_4_checked, root5Node12Step1Chunk3_5_checked, root5Node12Step1Chunk4_0_checked, root5Node12Step1Chunk4_1_checked, root5Node12Step1Chunk4_2_checked, root5Node12Step1Chunk4_3_checked, root5Node12Step1Chunk4_4_checked, root5Node12Step1Chunk4_5_checked, root5Node12Step1Chunk5_0_checked, root5Node12Step1Chunk5_1_checked, root5Node12Step1Chunk5_2_checked, root5Node12Step1Chunk5_3_checked, root5Node12Step1Chunk5_4_checked, root5Node12Step1Chunk5_5_checked, root5Node12Step1Chunk6_0_checked, root5Node12Step1Chunk6_1_checked, root5Node12Step1Chunk6_2_checked, root5Node12Step1Chunk6_3_checked, root5Node12Step1Chunk6_4_checked, root5Node12Step1Chunk6_5_checked, root5Node12Step1Chunk7_0_checked, root5Node12Step1Chunk7_1_checked, root5Node12Step1Chunk7_2_checked, root5Node12Step1Chunk7_3_checked, root5Node12Step1Chunk7_4_checked, root5Node12Step1Chunk7_5_checked, root5Node12Step1Chunk8_0_checked, root5Node12Step1Chunk8_1_checked, root5Node12Step1Chunk8_2_checked, root5Node12Step1Chunk8_3_checked, root5Node12Step1Chunk8_4_checked, root5Node12Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node12Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node12Domains1 (.output 5) = true := by decide
def root5Node13Domains0 : Domains 61 State := restrict root5Node11Domains0 4 (7,1)
def root5Node13Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node13Domains0_fast_eq : root5Node13Domains0 = expandDomains root5Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node13Domains0 v = expandDomains root5Node13Domains0Fast v from by decide) v
def root5Node13Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node13Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node13Domains1_fast_eq : root5Node13Domains1 = expandDomains root5Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node13Domains1 v = expandDomains root5Node13Domains1Fast v from by decide) v
theorem root5Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1_checked :
    checkReplacement table4 root5Node13Domains0 root5Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node13Step1Chunk0_0_checked, root5Node13Step1Chunk0_1_checked, root5Node13Step1Chunk0_2_checked, root5Node13Step1Chunk0_3_checked, root5Node13Step1Chunk0_4_checked, root5Node13Step1Chunk0_5_checked, root5Node13Step1Chunk1_0_checked, root5Node13Step1Chunk1_1_checked, root5Node13Step1Chunk1_2_checked, root5Node13Step1Chunk1_3_checked, root5Node13Step1Chunk1_4_checked, root5Node13Step1Chunk1_5_checked, root5Node13Step1Chunk2_0_checked, root5Node13Step1Chunk2_1_checked, root5Node13Step1Chunk2_2_checked, root5Node13Step1Chunk2_3_checked, root5Node13Step1Chunk2_4_checked, root5Node13Step1Chunk2_5_checked, root5Node13Step1Chunk3_0_checked, root5Node13Step1Chunk3_1_checked, root5Node13Step1Chunk3_2_checked, root5Node13Step1Chunk3_3_checked, root5Node13Step1Chunk3_4_checked, root5Node13Step1Chunk3_5_checked, root5Node13Step1Chunk4_0_checked, root5Node13Step1Chunk4_1_checked, root5Node13Step1Chunk4_2_checked, root5Node13Step1Chunk4_3_checked, root5Node13Step1Chunk4_4_checked, root5Node13Step1Chunk4_5_checked, root5Node13Step1Chunk5_0_checked, root5Node13Step1Chunk5_1_checked, root5Node13Step1Chunk5_2_checked, root5Node13Step1Chunk5_3_checked, root5Node13Step1Chunk5_4_checked, root5Node13Step1Chunk5_5_checked, root5Node13Step1Chunk6_0_checked, root5Node13Step1Chunk6_1_checked, root5Node13Step1Chunk6_2_checked, root5Node13Step1Chunk6_3_checked, root5Node13Step1Chunk6_4_checked, root5Node13Step1Chunk6_5_checked, root5Node13Step1Chunk7_0_checked, root5Node13Step1Chunk7_1_checked, root5Node13Step1Chunk7_2_checked, root5Node13Step1Chunk7_3_checked, root5Node13Step1Chunk7_4_checked, root5Node13Step1Chunk7_5_checked, root5Node13Step1Chunk8_0_checked, root5Node13Step1Chunk8_1_checked, root5Node13Step1Chunk8_2_checked, root5Node13Step1Chunk8_3_checked, root5Node13Step1Chunk8_4_checked, root5Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node13Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node13Domains1 (.output 6) = true := by decide
def root5Node14Domains0 : Domains 61 State := restrict root5Node0Domains4 28 (7,3)
def root5Node14Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(4,3),(7,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 9 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(7,4),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4),(6,5)]
  | 37 => some [(0,4),(1,2),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5),(7,5),(8,5)]
  | 44 => some [(0,3),(1,0),(7,0)]
  | 45 => some [(4,3),(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => some [(4,2),(4,4),(8,2)]
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node14Domains0_fast_eq : root5Node14Domains0 = expandDomains root5Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node14Domains0 v = expandDomains root5Node14Domains0Fast v from by decide) v
def root5Node14Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(5,2),(5,5),(8,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(4,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,5),(7,5)]
  | 9 => [(0,3),(1,0),(3,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1),(4,5)]
  | 11 => [(0,5),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(8,4)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(1,0),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => [(5,1),(5,4),(8,1),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(5,1),(5,4),(8,1),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
  | 43 => [(5,5),(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1),(5,1),(8,1)]
  | 49 => [(0,1),(0,2),(6,5)]
  | 50 => [(4,2),(4,4),(8,2)]
  | 51 => [(1,4),(5,0),(5,3)]
  | 52 => [(0,5),(4,5),(5,5),(8,5)]
  | 53 => [(2,0),(7,0)]
  | 54 => [(7,3),(8,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1),(4,4),(7,2)]
  | 59 => [(0,1),(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,2),(6,3)]
def root5Node14Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(5,2),(5,5),(8,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,5),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(8,4)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
  | 43 => some [(5,5),(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1),(5,1),(8,1)]
  | 49 => some [(0,1),(0,2),(6,5)]
  | 50 => some [(4,2),(4,4),(8,2)]
  | 51 => some [(1,4),(5,0),(5,3)]
  | 52 => some [(0,5),(4,5),(5,5),(8,5)]
  | 53 => some [(2,0),(7,0)]
  | 54 => some [(7,3),(8,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1),(4,4),(7,2)]
  | 59 => some [(0,1),(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,2),(6,3)]
theorem root5Node14Domains1_fast_eq : root5Node14Domains1 = expandDomains root5Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node14Domains1 v = expandDomains root5Node14Domains1Fast v from by decide) v
theorem root5Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root5Node14Domains0 root5Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains0 root5Node14Domains1
    root5Node14Domains0Fast root5Node14Domains1Fast
    root5Node14Domains0_fast_eq root5Node14Domains1_fast_eq (by decide)
theorem root5Node14Step1_checked :
    checkReplacement table21 root5Node14Domains0 root5Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node14Step1Chunk0_0_checked, root5Node14Step1Chunk0_1_checked, root5Node14Step1Chunk0_2_checked, root5Node14Step1Chunk0_3_checked, root5Node14Step1Chunk0_4_checked, root5Node14Step1Chunk0_5_checked, root5Node14Step1Chunk1_0_checked, root5Node14Step1Chunk1_1_checked, root5Node14Step1Chunk1_2_checked, root5Node14Step1Chunk1_3_checked, root5Node14Step1Chunk1_4_checked, root5Node14Step1Chunk1_5_checked, root5Node14Step1Chunk2_0_checked, root5Node14Step1Chunk2_1_checked, root5Node14Step1Chunk2_2_checked, root5Node14Step1Chunk2_3_checked, root5Node14Step1Chunk2_4_checked, root5Node14Step1Chunk2_5_checked, root5Node14Step1Chunk3_0_checked, root5Node14Step1Chunk3_1_checked, root5Node14Step1Chunk3_2_checked, root5Node14Step1Chunk3_3_checked, root5Node14Step1Chunk3_4_checked, root5Node14Step1Chunk3_5_checked, root5Node14Step1Chunk4_0_checked, root5Node14Step1Chunk4_1_checked, root5Node14Step1Chunk4_2_checked, root5Node14Step1Chunk4_3_checked, root5Node14Step1Chunk4_4_checked, root5Node14Step1Chunk4_5_checked, root5Node14Step1Chunk5_0_checked, root5Node14Step1Chunk5_1_checked, root5Node14Step1Chunk5_2_checked, root5Node14Step1Chunk5_3_checked, root5Node14Step1Chunk5_4_checked, root5Node14Step1Chunk5_5_checked, root5Node14Step1Chunk6_0_checked, root5Node14Step1Chunk6_1_checked, root5Node14Step1Chunk6_2_checked, root5Node14Step1Chunk6_3_checked, root5Node14Step1Chunk6_4_checked, root5Node14Step1Chunk6_5_checked, root5Node14Step1Chunk7_0_checked, root5Node14Step1Chunk7_1_checked, root5Node14Step1Chunk7_2_checked, root5Node14Step1Chunk7_3_checked, root5Node14Step1Chunk7_4_checked, root5Node14Step1Chunk7_5_checked, root5Node14Step1Chunk8_0_checked, root5Node14Step1Chunk8_1_checked, root5Node14Step1Chunk8_2_checked, root5Node14Step1Chunk8_3_checked, root5Node14Step1Chunk8_4_checked, root5Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
