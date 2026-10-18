module

public import SpectreFinite.RadiusFourRoot5Part14
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node45Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(8,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root5Node45Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root5Node45Domains2_fast_eq : root5Node45Domains2 = expandDomains root5Node45Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node45Domains2 v = expandDomains root5Node45Domains2Fast v from by decide) v
theorem root5Node45Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root5Node45Domains1 root5Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains1 root5Node45Domains2
    root5Node45Domains1Fast root5Node45Domains2Fast
    root5Node45Domains1_fast_eq root5Node45Domains2_fast_eq (by decide)
theorem root5Node45Step2_checked :
    checkReplacement table39 root5Node45Domains1 root5Node45Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node45Step2Chunk0_0_checked, root5Node45Step2Chunk0_1_checked, root5Node45Step2Chunk0_2_checked, root5Node45Step2Chunk0_3_checked, root5Node45Step2Chunk0_4_checked, root5Node45Step2Chunk0_5_checked, root5Node45Step2Chunk1_0_checked, root5Node45Step2Chunk1_1_checked, root5Node45Step2Chunk1_2_checked, root5Node45Step2Chunk1_3_checked, root5Node45Step2Chunk1_4_checked, root5Node45Step2Chunk1_5_checked, root5Node45Step2Chunk2_0_checked, root5Node45Step2Chunk2_1_checked, root5Node45Step2Chunk2_2_checked, root5Node45Step2Chunk2_3_checked, root5Node45Step2Chunk2_4_checked, root5Node45Step2Chunk2_5_checked, root5Node45Step2Chunk3_0_checked, root5Node45Step2Chunk3_1_checked, root5Node45Step2Chunk3_2_checked, root5Node45Step2Chunk3_3_checked, root5Node45Step2Chunk3_4_checked, root5Node45Step2Chunk3_5_checked, root5Node45Step2Chunk4_0_checked, root5Node45Step2Chunk4_1_checked, root5Node45Step2Chunk4_2_checked, root5Node45Step2Chunk4_3_checked, root5Node45Step2Chunk4_4_checked, root5Node45Step2Chunk4_5_checked, root5Node45Step2Chunk5_0_checked, root5Node45Step2Chunk5_1_checked, root5Node45Step2Chunk5_2_checked, root5Node45Step2Chunk5_3_checked, root5Node45Step2Chunk5_4_checked, root5Node45Step2Chunk5_5_checked, root5Node45Step2Chunk6_0_checked, root5Node45Step2Chunk6_1_checked, root5Node45Step2Chunk6_2_checked, root5Node45Step2Chunk6_3_checked, root5Node45Step2Chunk6_4_checked, root5Node45Step2Chunk6_5_checked, root5Node45Step2Chunk7_0_checked, root5Node45Step2Chunk7_1_checked, root5Node45Step2Chunk7_2_checked, root5Node45Step2Chunk7_3_checked, root5Node45Step2Chunk7_4_checked, root5Node45Step2Chunk7_5_checked, root5Node45Step2Chunk8_0_checked, root5Node45Step2Chunk8_1_checked, root5Node45Step2Chunk8_2_checked, root5Node45Step2Chunk8_3_checked, root5Node45Step2Chunk8_4_checked, root5Node45Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node46Domains0 : Domains 61 State := restrict root5Node45Domains2 60 (1,3)
def root5Node46Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3)]
theorem root5Node46Domains0_fast_eq : root5Node46Domains0 = expandDomains root5Node46Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node46Domains0 v = expandDomains root5Node46Domains0Fast v from by decide) v
theorem root5Node46Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node46Domains0 (.output 22) = true := by decide
def root5Node47Domains0 : Domains 61 State := restrict root5Node45Domains2 60 (6,3)
def root5Node47Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node47Domains0_fast_eq : root5Node47Domains0 = expandDomains root5Node47Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node47Domains0 v = expandDomains root5Node47Domains0Fast v from by decide) v
theorem root5Node47Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node47Domains0 (.output 23) = true := by decide
def root5Node48Domains0 : Domains 61 State := restrict root5Node14Domains4 6 (8,0)
def root5Node48Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(5,2),(5,5),(8,5)]
  | 6 => some [(8,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1)]
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
  | 25 => some [(5,1),(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1),(8,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node48Domains0_fast_eq : root5Node48Domains0 = expandDomains root5Node48Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node48Domains0 v = expandDomains root5Node48Domains0Fast v from by decide) v
def root5Node48Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(6,2)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0),(3,0)]
  | 10 => [(2,1),(2,5)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(0,2),(1,0),(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1),(5,4),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1),(8,1)]
  | 49 => [(0,1),(6,5)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(5,0),(5,3)]
  | 52 => [(4,5),(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4)]
  | 57 => [(0,0),(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root5Node48Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0),(3,0)]
  | 10 => some [(2,1),(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1),(8,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node48Domains1_fast_eq : root5Node48Domains1 = expandDomains root5Node48Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node48Domains1 v = expandDomains root5Node48Domains1Fast v from by decide) v
theorem root5Node48Step1Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root5Node48Domains0 root5Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains0 root5Node48Domains1
    root5Node48Domains0Fast root5Node48Domains1Fast
    root5Node48Domains0_fast_eq root5Node48Domains1_fast_eq (by decide)
theorem root5Node48Step1_checked :
    checkReplacement table14 root5Node48Domains0 root5Node48Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node48Step1Chunk0_0_checked, root5Node48Step1Chunk0_1_checked, root5Node48Step1Chunk0_2_checked, root5Node48Step1Chunk0_3_checked, root5Node48Step1Chunk0_4_checked, root5Node48Step1Chunk0_5_checked, root5Node48Step1Chunk1_0_checked, root5Node48Step1Chunk1_1_checked, root5Node48Step1Chunk1_2_checked, root5Node48Step1Chunk1_3_checked, root5Node48Step1Chunk1_4_checked, root5Node48Step1Chunk1_5_checked, root5Node48Step1Chunk2_0_checked, root5Node48Step1Chunk2_1_checked, root5Node48Step1Chunk2_2_checked, root5Node48Step1Chunk2_3_checked, root5Node48Step1Chunk2_4_checked, root5Node48Step1Chunk2_5_checked, root5Node48Step1Chunk3_0_checked, root5Node48Step1Chunk3_1_checked, root5Node48Step1Chunk3_2_checked, root5Node48Step1Chunk3_3_checked, root5Node48Step1Chunk3_4_checked, root5Node48Step1Chunk3_5_checked, root5Node48Step1Chunk4_0_checked, root5Node48Step1Chunk4_1_checked, root5Node48Step1Chunk4_2_checked, root5Node48Step1Chunk4_3_checked, root5Node48Step1Chunk4_4_checked, root5Node48Step1Chunk4_5_checked, root5Node48Step1Chunk5_0_checked, root5Node48Step1Chunk5_1_checked, root5Node48Step1Chunk5_2_checked, root5Node48Step1Chunk5_3_checked, root5Node48Step1Chunk5_4_checked, root5Node48Step1Chunk5_5_checked, root5Node48Step1Chunk6_0_checked, root5Node48Step1Chunk6_1_checked, root5Node48Step1Chunk6_2_checked, root5Node48Step1Chunk6_3_checked, root5Node48Step1Chunk6_4_checked, root5Node48Step1Chunk6_5_checked, root5Node48Step1Chunk7_0_checked, root5Node48Step1Chunk7_1_checked, root5Node48Step1Chunk7_2_checked, root5Node48Step1Chunk7_3_checked, root5Node48Step1Chunk7_4_checked, root5Node48Step1Chunk7_5_checked, root5Node48Step1Chunk8_0_checked, root5Node48Step1Chunk8_1_checked, root5Node48Step1Chunk8_2_checked, root5Node48Step1Chunk8_3_checked, root5Node48Step1Chunk8_4_checked, root5Node48Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node48Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(6,2)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0),(3,0)]
  | 10 => [(2,1),(2,5)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(0,2),(1,0),(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(5,0),(5,3)]
  | 52 => [(4,5),(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4)]
  | 57 => [(0,0),(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node48Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0),(3,0)]
  | 10 => some [(2,1),(2,5)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node48Domains2_fast_eq : root5Node48Domains2 = expandDomains root5Node48Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node48Domains2 v = expandDomains root5Node48Domains2Fast v from by decide) v
theorem root5Node48Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root5Node48Domains1 root5Node48Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node48Domains1 root5Node48Domains2
    root5Node48Domains1Fast root5Node48Domains2Fast
    root5Node48Domains1_fast_eq root5Node48Domains2_fast_eq (by decide)
theorem root5Node48Step2_checked :
    checkReplacement table40 root5Node48Domains1 root5Node48Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node48Step2Chunk0_0_checked, root5Node48Step2Chunk0_1_checked, root5Node48Step2Chunk0_2_checked, root5Node48Step2Chunk0_3_checked, root5Node48Step2Chunk0_4_checked, root5Node48Step2Chunk0_5_checked, root5Node48Step2Chunk1_0_checked, root5Node48Step2Chunk1_1_checked, root5Node48Step2Chunk1_2_checked, root5Node48Step2Chunk1_3_checked, root5Node48Step2Chunk1_4_checked, root5Node48Step2Chunk1_5_checked, root5Node48Step2Chunk2_0_checked, root5Node48Step2Chunk2_1_checked, root5Node48Step2Chunk2_2_checked, root5Node48Step2Chunk2_3_checked, root5Node48Step2Chunk2_4_checked, root5Node48Step2Chunk2_5_checked, root5Node48Step2Chunk3_0_checked, root5Node48Step2Chunk3_1_checked, root5Node48Step2Chunk3_2_checked, root5Node48Step2Chunk3_3_checked, root5Node48Step2Chunk3_4_checked, root5Node48Step2Chunk3_5_checked, root5Node48Step2Chunk4_0_checked, root5Node48Step2Chunk4_1_checked, root5Node48Step2Chunk4_2_checked, root5Node48Step2Chunk4_3_checked, root5Node48Step2Chunk4_4_checked, root5Node48Step2Chunk4_5_checked, root5Node48Step2Chunk5_0_checked, root5Node48Step2Chunk5_1_checked, root5Node48Step2Chunk5_2_checked, root5Node48Step2Chunk5_3_checked, root5Node48Step2Chunk5_4_checked, root5Node48Step2Chunk5_5_checked, root5Node48Step2Chunk6_0_checked, root5Node48Step2Chunk6_1_checked, root5Node48Step2Chunk6_2_checked, root5Node48Step2Chunk6_3_checked, root5Node48Step2Chunk6_4_checked, root5Node48Step2Chunk6_5_checked, root5Node48Step2Chunk7_0_checked, root5Node48Step2Chunk7_1_checked, root5Node48Step2Chunk7_2_checked, root5Node48Step2Chunk7_3_checked, root5Node48Step2Chunk7_4_checked, root5Node48Step2Chunk7_5_checked, root5Node48Step2Chunk8_0_checked, root5Node48Step2Chunk8_1_checked, root5Node48Step2Chunk8_2_checked, root5Node48Step2Chunk8_3_checked, root5Node48Step2Chunk8_4_checked, root5Node48Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
