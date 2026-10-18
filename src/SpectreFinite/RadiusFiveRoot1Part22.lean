module

public import SpectreFinite.RadiusFiveRoot1Part21
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable53
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node54Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(2,2)]
  | 25 => [(3,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,1)]
  | 31 => [(4,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(5,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(8,2)]
  | 83 => [(5,0)]
  | 84 => [(4,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(5,4)]
  | _ => [(0,0)]
def root1Node54Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(8,2)]
  | 83 => some [(5,0)]
  | 84 => some [(4,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(5,4)]
  | _ => some [(0,0)]
theorem root1Node54Domains2_fast_eq : root1Node54Domains2 = expandDomains root1Node54Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node54Domains2 v = expandDomains root1Node54Domains2Fast v from by decide) v
theorem root1Node54Step2Chunk0_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk0_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk0_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk0_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk0_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk0_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk1_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk1_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk1_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk1_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk1_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk1_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk2_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk2_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk2_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk2_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk2_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk2_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk3_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk3_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk3_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk3_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk3_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk3_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk4_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk4_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk4_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk4_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk4_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk4_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk5_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk5_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk5_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk5_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk5_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk5_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk6_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk6_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk6_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk6_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk6_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk6_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk7_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk7_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk7_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk7_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk7_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk7_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk8_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_0⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk8_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_1⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk8_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_2⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk8_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_3⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk8_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_4⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Chunk8_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_5⟩
      root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq (by decide)
theorem root1Node54Step2Narrowing_checked :
    checkNarrowing table53 root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkNarrowing_flatten table53Scope [table53Rows0_0,table53Rows0_1,table53Rows0_2,table53Rows0_3,table53Rows0_4,table53Rows0_5,table53Rows1_0,table53Rows1_1,table53Rows1_2,table53Rows1_3,table53Rows1_4,table53Rows1_5,table53Rows2_0,table53Rows2_1,table53Rows2_2,table53Rows2_3,table53Rows2_4,table53Rows2_5,table53Rows3_0,table53Rows3_1,table53Rows3_2,table53Rows3_3,table53Rows3_4,table53Rows3_5,table53Rows4_0,table53Rows4_1,table53Rows4_2,table53Rows4_3,table53Rows4_4,table53Rows4_5,table53Rows5_0,table53Rows5_1,table53Rows5_2,table53Rows5_3,table53Rows5_4,table53Rows5_5,table53Rows6_0,table53Rows6_1,table53Rows6_2,table53Rows6_3,table53Rows6_4,table53Rows6_5,table53Rows7_0,table53Rows7_1,table53Rows7_2,table53Rows7_3,table53Rows7_4,table53Rows7_5,table53Rows8_0,table53Rows8_1,table53Rows8_2,table53Rows8_3,table53Rows8_4,table53Rows8_5]
    root1Node54Domains1 root1Node54Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node54Step2Chunk0_0_checked, root1Node54Step2Chunk0_1_checked, root1Node54Step2Chunk0_2_checked, root1Node54Step2Chunk0_3_checked, root1Node54Step2Chunk0_4_checked, root1Node54Step2Chunk0_5_checked, root1Node54Step2Chunk1_0_checked, root1Node54Step2Chunk1_1_checked, root1Node54Step2Chunk1_2_checked, root1Node54Step2Chunk1_3_checked, root1Node54Step2Chunk1_4_checked, root1Node54Step2Chunk1_5_checked, root1Node54Step2Chunk2_0_checked, root1Node54Step2Chunk2_1_checked, root1Node54Step2Chunk2_2_checked, root1Node54Step2Chunk2_3_checked, root1Node54Step2Chunk2_4_checked, root1Node54Step2Chunk2_5_checked, root1Node54Step2Chunk3_0_checked, root1Node54Step2Chunk3_1_checked, root1Node54Step2Chunk3_2_checked, root1Node54Step2Chunk3_3_checked, root1Node54Step2Chunk3_4_checked, root1Node54Step2Chunk3_5_checked, root1Node54Step2Chunk4_0_checked, root1Node54Step2Chunk4_1_checked, root1Node54Step2Chunk4_2_checked, root1Node54Step2Chunk4_3_checked, root1Node54Step2Chunk4_4_checked, root1Node54Step2Chunk4_5_checked, root1Node54Step2Chunk5_0_checked, root1Node54Step2Chunk5_1_checked, root1Node54Step2Chunk5_2_checked, root1Node54Step2Chunk5_3_checked, root1Node54Step2Chunk5_4_checked, root1Node54Step2Chunk5_5_checked, root1Node54Step2Chunk6_0_checked, root1Node54Step2Chunk6_1_checked, root1Node54Step2Chunk6_2_checked, root1Node54Step2Chunk6_3_checked, root1Node54Step2Chunk6_4_checked, root1Node54Step2Chunk6_5_checked, root1Node54Step2Chunk7_0_checked, root1Node54Step2Chunk7_1_checked, root1Node54Step2Chunk7_2_checked, root1Node54Step2Chunk7_3_checked, root1Node54Step2Chunk7_4_checked, root1Node54Step2Chunk7_5_checked, root1Node54Step2Chunk8_0_checked, root1Node54Step2Chunk8_1_checked, root1Node54Step2Chunk8_2_checked, root1Node54Step2Chunk8_3_checked, root1Node54Step2Chunk8_4_checked, root1Node54Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node54Step2_checked :
    checkReplacement table53 root1Node54Domains1 root1Node54Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node54Domains1 root1Node54Domains2
    root1Node54Domains1Fast root1Node54Domains2Fast
    root1Node54Domains1_fast_eq root1Node54Domains2_fast_eq
    root1Node54Step2Narrowing_checked (by decide)
theorem root1Node54Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node54Domains2 (.output 26) = true := by decide
def root1Node55Domains0 : Domains 91 State := restrict root1Node53Domains1 50 (7,5)
def root1Node55Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5),(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(7,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root1Node55Domains0_fast_eq : root1Node55Domains0 = expandDomains root1Node55Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node55Domains0 v = expandDomains root1Node55Domains0Fast v from by decide) v
def root1Node55Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(2,2)]
  | 25 => [(3,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,1)]
  | 31 => [(4,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(8,0)]
  | 60 => [(7,3)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(6,4)]
  | 70 => [(5,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(7,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3),(6,3)]
  | 82 => [(7,2),(8,2)]
  | 83 => [(4,0),(8,0)]
  | 84 => [(7,3)]
  | 85 => [(1,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(0,2),(6,5)]
  | 88 => [(0,4),(1,1)]
  | 89 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
def root1Node55Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(8,0)]
  | 84 => some [(7,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root1Node55Domains1_fast_eq : root1Node55Domains1 = expandDomains root1Node55Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node55Domains1 v = expandDomains root1Node55Domains1Fast v from by decide) v
theorem root1Node55Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq (by decide)
theorem root1Node55Step1Narrowing_checked :
    checkNarrowing table57 root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root1Node55Domains0 root1Node55Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node55Step1Chunk0_0_checked, root1Node55Step1Chunk0_1_checked, root1Node55Step1Chunk0_2_checked, root1Node55Step1Chunk0_3_checked, root1Node55Step1Chunk0_4_checked, root1Node55Step1Chunk0_5_checked, root1Node55Step1Chunk1_0_checked, root1Node55Step1Chunk1_1_checked, root1Node55Step1Chunk1_2_checked, root1Node55Step1Chunk1_3_checked, root1Node55Step1Chunk1_4_checked, root1Node55Step1Chunk1_5_checked, root1Node55Step1Chunk2_0_checked, root1Node55Step1Chunk2_1_checked, root1Node55Step1Chunk2_2_checked, root1Node55Step1Chunk2_3_checked, root1Node55Step1Chunk2_4_checked, root1Node55Step1Chunk2_5_checked, root1Node55Step1Chunk3_0_checked, root1Node55Step1Chunk3_1_checked, root1Node55Step1Chunk3_2_checked, root1Node55Step1Chunk3_3_checked, root1Node55Step1Chunk3_4_checked, root1Node55Step1Chunk3_5_checked, root1Node55Step1Chunk4_0_checked, root1Node55Step1Chunk4_1_checked, root1Node55Step1Chunk4_2_checked, root1Node55Step1Chunk4_3_checked, root1Node55Step1Chunk4_4_checked, root1Node55Step1Chunk4_5_checked, root1Node55Step1Chunk5_0_checked, root1Node55Step1Chunk5_1_checked, root1Node55Step1Chunk5_2_checked, root1Node55Step1Chunk5_3_checked, root1Node55Step1Chunk5_4_checked, root1Node55Step1Chunk5_5_checked, root1Node55Step1Chunk6_0_checked, root1Node55Step1Chunk6_1_checked, root1Node55Step1Chunk6_2_checked, root1Node55Step1Chunk6_3_checked, root1Node55Step1Chunk6_4_checked, root1Node55Step1Chunk6_5_checked, root1Node55Step1Chunk7_0_checked, root1Node55Step1Chunk7_1_checked, root1Node55Step1Chunk7_2_checked, root1Node55Step1Chunk7_3_checked, root1Node55Step1Chunk7_4_checked, root1Node55Step1Chunk7_5_checked, root1Node55Step1Chunk8_0_checked, root1Node55Step1Chunk8_1_checked, root1Node55Step1Chunk8_2_checked, root1Node55Step1Chunk8_3_checked, root1Node55Step1Chunk8_4_checked, root1Node55Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node55Step1_checked :
    checkReplacement table57 root1Node55Domains0 root1Node55Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node55Domains0 root1Node55Domains1
    root1Node55Domains0Fast root1Node55Domains1Fast
    root1Node55Domains0_fast_eq root1Node55Domains1_fast_eq
    root1Node55Step1Narrowing_checked (by decide)
def root1Node56Domains0 : Domains 91 State := restrict root1Node55Domains1 81 (1,3)
def root1Node56Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(8,0)]
  | 84 => some [(7,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root1Node56Domains0_fast_eq : root1Node56Domains0 = expandDomains root1Node56Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node56Domains0 v = expandDomains root1Node56Domains0Fast v from by decide) v
def root1Node56Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(2,2)]
  | 25 => [(3,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,1)]
  | 31 => [(4,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(8,0)]
  | 60 => [(7,3)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(6,4)]
  | 70 => [(5,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(7,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(8,2)]
  | 83 => [(8,0)]
  | 84 => [(7,3)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(5,4)]
  | _ => [(6,4)]
def root1Node56Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(8,2)]
  | 83 => some [(8,0)]
  | 84 => some [(7,3)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(5,4)]
  | _ => some [(6,4)]
theorem root1Node56Domains1_fast_eq : root1Node56Domains1 = expandDomains root1Node56Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node56Domains1 v = expandDomains root1Node56Domains1Fast v from by decide) v
theorem root1Node56Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq (by decide)
theorem root1Node56Step1Narrowing_checked :
    checkNarrowing table56 root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root1Node56Domains0 root1Node56Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node56Step1Chunk0_0_checked, root1Node56Step1Chunk0_1_checked, root1Node56Step1Chunk0_2_checked, root1Node56Step1Chunk0_3_checked, root1Node56Step1Chunk0_4_checked, root1Node56Step1Chunk0_5_checked, root1Node56Step1Chunk1_0_checked, root1Node56Step1Chunk1_1_checked, root1Node56Step1Chunk1_2_checked, root1Node56Step1Chunk1_3_checked, root1Node56Step1Chunk1_4_checked, root1Node56Step1Chunk1_5_checked, root1Node56Step1Chunk2_0_checked, root1Node56Step1Chunk2_1_checked, root1Node56Step1Chunk2_2_checked, root1Node56Step1Chunk2_3_checked, root1Node56Step1Chunk2_4_checked, root1Node56Step1Chunk2_5_checked, root1Node56Step1Chunk3_0_checked, root1Node56Step1Chunk3_1_checked, root1Node56Step1Chunk3_2_checked, root1Node56Step1Chunk3_3_checked, root1Node56Step1Chunk3_4_checked, root1Node56Step1Chunk3_5_checked, root1Node56Step1Chunk4_0_checked, root1Node56Step1Chunk4_1_checked, root1Node56Step1Chunk4_2_checked, root1Node56Step1Chunk4_3_checked, root1Node56Step1Chunk4_4_checked, root1Node56Step1Chunk4_5_checked, root1Node56Step1Chunk5_0_checked, root1Node56Step1Chunk5_1_checked, root1Node56Step1Chunk5_2_checked, root1Node56Step1Chunk5_3_checked, root1Node56Step1Chunk5_4_checked, root1Node56Step1Chunk5_5_checked, root1Node56Step1Chunk6_0_checked, root1Node56Step1Chunk6_1_checked, root1Node56Step1Chunk6_2_checked, root1Node56Step1Chunk6_3_checked, root1Node56Step1Chunk6_4_checked, root1Node56Step1Chunk6_5_checked, root1Node56Step1Chunk7_0_checked, root1Node56Step1Chunk7_1_checked, root1Node56Step1Chunk7_2_checked, root1Node56Step1Chunk7_3_checked, root1Node56Step1Chunk7_4_checked, root1Node56Step1Chunk7_5_checked, root1Node56Step1Chunk8_0_checked, root1Node56Step1Chunk8_1_checked, root1Node56Step1Chunk8_2_checked, root1Node56Step1Chunk8_3_checked, root1Node56Step1Chunk8_4_checked, root1Node56Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node56Step1_checked :
    checkReplacement table56 root1Node56Domains0 root1Node56Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node56Domains0 root1Node56Domains1
    root1Node56Domains0Fast root1Node56Domains1Fast
    root1Node56Domains0_fast_eq root1Node56Domains1_fast_eq
    root1Node56Step1Narrowing_checked (by decide)
theorem root1Node56Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node56Domains1 (.output 27) = true := by decide
def root1Node57Domains0 : Domains 91 State := restrict root1Node55Domains1 81 (6,3)
def root1Node57Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(8,0)]
  | 84 => some [(7,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root1Node57Domains0_fast_eq : root1Node57Domains0 = expandDomains root1Node57Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node57Domains0 v = expandDomains root1Node57Domains0Fast v from by decide) v
def root1Node57Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(2,2)]
  | 25 => [(3,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,1)]
  | 31 => [(4,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(8,0)]
  | 60 => [(7,3)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(6,4)]
  | 70 => [(5,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(7,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(6,3)]
  | 82 => [(7,2)]
  | 83 => [(4,0)]
  | 84 => [(7,3)]
  | 85 => [(1,1)]
  | 86 => [(4,1)]
  | 87 => [(0,2)]
  | 88 => [(1,1)]
  | 89 => [(5,1)]
  | _ => [(0,1)]
def root1Node57Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(2,2)]
  | 25 => some [(3,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,1)]
  | 31 => some [(4,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(7,2)]
  | 83 => some [(4,0)]
  | 84 => some [(7,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1)]
  | 87 => some [(0,2)]
  | 88 => some [(1,1)]
  | 89 => some [(5,1)]
  | _ => some [(0,1)]
theorem root1Node57Domains1_fast_eq : root1Node57Domains1 = expandDomains root1Node57Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node57Domains1 v = expandDomains root1Node57Domains1Fast v from by decide) v
theorem root1Node57Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Narrowing_checked :
    checkNarrowing table56 root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root1Node57Domains0 root1Node57Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node57Step1Chunk0_0_checked, root1Node57Step1Chunk0_1_checked, root1Node57Step1Chunk0_2_checked, root1Node57Step1Chunk0_3_checked, root1Node57Step1Chunk0_4_checked, root1Node57Step1Chunk0_5_checked, root1Node57Step1Chunk1_0_checked, root1Node57Step1Chunk1_1_checked, root1Node57Step1Chunk1_2_checked, root1Node57Step1Chunk1_3_checked, root1Node57Step1Chunk1_4_checked, root1Node57Step1Chunk1_5_checked, root1Node57Step1Chunk2_0_checked, root1Node57Step1Chunk2_1_checked, root1Node57Step1Chunk2_2_checked, root1Node57Step1Chunk2_3_checked, root1Node57Step1Chunk2_4_checked, root1Node57Step1Chunk2_5_checked, root1Node57Step1Chunk3_0_checked, root1Node57Step1Chunk3_1_checked, root1Node57Step1Chunk3_2_checked, root1Node57Step1Chunk3_3_checked, root1Node57Step1Chunk3_4_checked, root1Node57Step1Chunk3_5_checked, root1Node57Step1Chunk4_0_checked, root1Node57Step1Chunk4_1_checked, root1Node57Step1Chunk4_2_checked, root1Node57Step1Chunk4_3_checked, root1Node57Step1Chunk4_4_checked, root1Node57Step1Chunk4_5_checked, root1Node57Step1Chunk5_0_checked, root1Node57Step1Chunk5_1_checked, root1Node57Step1Chunk5_2_checked, root1Node57Step1Chunk5_3_checked, root1Node57Step1Chunk5_4_checked, root1Node57Step1Chunk5_5_checked, root1Node57Step1Chunk6_0_checked, root1Node57Step1Chunk6_1_checked, root1Node57Step1Chunk6_2_checked, root1Node57Step1Chunk6_3_checked, root1Node57Step1Chunk6_4_checked, root1Node57Step1Chunk6_5_checked, root1Node57Step1Chunk7_0_checked, root1Node57Step1Chunk7_1_checked, root1Node57Step1Chunk7_2_checked, root1Node57Step1Chunk7_3_checked, root1Node57Step1Chunk7_4_checked, root1Node57Step1Chunk7_5_checked, root1Node57Step1Chunk8_0_checked, root1Node57Step1Chunk8_1_checked, root1Node57Step1Chunk8_2_checked, root1Node57Step1Chunk8_3_checked, root1Node57Step1Chunk8_4_checked, root1Node57Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node57Step1_checked :
    checkReplacement table56 root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq
    root1Node57Step1Narrowing_checked (by decide)
theorem root1Node57Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node57Domains1 (.output 28) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
