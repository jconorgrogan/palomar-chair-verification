module

public import SpectreFinite.RadiusFiveRoot1Part39
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable41
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node96Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(7,0)]
  | 30 => [(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,3)]
  | 41 => [(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,0)]
  | 83 => [(7,3)]
  | 84 => [(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(3,1)]
  | 89 => [(0,1)]
  | _ => [(6,2)]
def root1Node96Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(7,0)]
  | 30 => some [(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0)]
  | 83 => some [(7,3)]
  | 84 => some [(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1)]
  | 89 => some [(0,1)]
  | _ => some [(6,2)]
theorem root1Node96Domains2_fast_eq : root1Node96Domains2 = expandDomains root1Node96Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node96Domains2 v = expandDomains root1Node96Domains2Fast v from by decide) v
theorem root1Node96Step2Chunk0_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk0_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk0_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk0_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk0_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk0_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk1_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk1_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk1_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk1_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk1_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk1_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk2_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk2_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk2_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk2_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk2_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk2_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk3_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk3_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk3_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk3_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk3_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk3_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk4_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk4_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk4_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk4_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk4_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk4_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk5_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk5_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk5_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk5_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk5_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk5_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk6_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk6_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk6_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk6_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk6_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk6_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk7_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk7_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk7_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk7_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk7_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk7_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk8_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_0⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk8_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_1⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk8_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_2⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk8_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_3⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk8_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_4⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Chunk8_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_5⟩
      root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq (by decide)
theorem root1Node96Step2Narrowing_checked :
    checkNarrowing table41 root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkNarrowing_flatten table41Scope [table41Rows0_0,table41Rows0_1,table41Rows0_2,table41Rows0_3,table41Rows0_4,table41Rows0_5,table41Rows1_0,table41Rows1_1,table41Rows1_2,table41Rows1_3,table41Rows1_4,table41Rows1_5,table41Rows2_0,table41Rows2_1,table41Rows2_2,table41Rows2_3,table41Rows2_4,table41Rows2_5,table41Rows3_0,table41Rows3_1,table41Rows3_2,table41Rows3_3,table41Rows3_4,table41Rows3_5,table41Rows4_0,table41Rows4_1,table41Rows4_2,table41Rows4_3,table41Rows4_4,table41Rows4_5,table41Rows5_0,table41Rows5_1,table41Rows5_2,table41Rows5_3,table41Rows5_4,table41Rows5_5,table41Rows6_0,table41Rows6_1,table41Rows6_2,table41Rows6_3,table41Rows6_4,table41Rows6_5,table41Rows7_0,table41Rows7_1,table41Rows7_2,table41Rows7_3,table41Rows7_4,table41Rows7_5,table41Rows8_0,table41Rows8_1,table41Rows8_2,table41Rows8_3,table41Rows8_4,table41Rows8_5]
    root1Node96Domains1 root1Node96Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node96Step2Chunk0_0_checked, root1Node96Step2Chunk0_1_checked, root1Node96Step2Chunk0_2_checked, root1Node96Step2Chunk0_3_checked, root1Node96Step2Chunk0_4_checked, root1Node96Step2Chunk0_5_checked, root1Node96Step2Chunk1_0_checked, root1Node96Step2Chunk1_1_checked, root1Node96Step2Chunk1_2_checked, root1Node96Step2Chunk1_3_checked, root1Node96Step2Chunk1_4_checked, root1Node96Step2Chunk1_5_checked, root1Node96Step2Chunk2_0_checked, root1Node96Step2Chunk2_1_checked, root1Node96Step2Chunk2_2_checked, root1Node96Step2Chunk2_3_checked, root1Node96Step2Chunk2_4_checked, root1Node96Step2Chunk2_5_checked, root1Node96Step2Chunk3_0_checked, root1Node96Step2Chunk3_1_checked, root1Node96Step2Chunk3_2_checked, root1Node96Step2Chunk3_3_checked, root1Node96Step2Chunk3_4_checked, root1Node96Step2Chunk3_5_checked, root1Node96Step2Chunk4_0_checked, root1Node96Step2Chunk4_1_checked, root1Node96Step2Chunk4_2_checked, root1Node96Step2Chunk4_3_checked, root1Node96Step2Chunk4_4_checked, root1Node96Step2Chunk4_5_checked, root1Node96Step2Chunk5_0_checked, root1Node96Step2Chunk5_1_checked, root1Node96Step2Chunk5_2_checked, root1Node96Step2Chunk5_3_checked, root1Node96Step2Chunk5_4_checked, root1Node96Step2Chunk5_5_checked, root1Node96Step2Chunk6_0_checked, root1Node96Step2Chunk6_1_checked, root1Node96Step2Chunk6_2_checked, root1Node96Step2Chunk6_3_checked, root1Node96Step2Chunk6_4_checked, root1Node96Step2Chunk6_5_checked, root1Node96Step2Chunk7_0_checked, root1Node96Step2Chunk7_1_checked, root1Node96Step2Chunk7_2_checked, root1Node96Step2Chunk7_3_checked, root1Node96Step2Chunk7_4_checked, root1Node96Step2Chunk7_5_checked, root1Node96Step2Chunk8_0_checked, root1Node96Step2Chunk8_1_checked, root1Node96Step2Chunk8_2_checked, root1Node96Step2Chunk8_3_checked, root1Node96Step2Chunk8_4_checked, root1Node96Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node96Step2_checked :
    checkReplacement table41 root1Node96Domains1 root1Node96Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node96Domains1 root1Node96Domains2
    root1Node96Domains1Fast root1Node96Domains2Fast
    root1Node96Domains1_fast_eq root1Node96Domains2_fast_eq
    root1Node96Step2Narrowing_checked (by decide)
theorem root1Node96Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node96Domains2 (.output 47) = true := by decide
def root1Node97Domains0 : Domains 91 State := restrict root1Node95Domains3 20 (7,5)
def root1Node97Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0)]
  | 59 => some [(5,3),(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,0),(2,4),(4,4)]
  | 83 => some [(0,0),(1,3),(7,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(3,1),(7,1)]
  | 89 => some [(0,1),(1,5),(6,5)]
  | _ => some [(0,4),(6,1),(6,2)]
theorem root1Node97Domains0_fast_eq : root1Node97Domains0 = expandDomains root1Node97Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node97Domains0 v = expandDomains root1Node97Domains0Fast v from by decide) v
def root1Node97Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0),(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(1,1),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,1),(6,4)]
  | 67 => [(1,2),(6,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(3,5),(5,5)]
  | 75 => [(0,3),(1,0)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,5),(6,2)]
  | 79 => [(4,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(2,4),(4,4)]
  | 83 => [(0,0),(1,3)]
  | 84 => [(3,2),(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(6,5)]
  | _ => [(0,4),(6,1)]
def root1Node97Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4),(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node97Domains1_fast_eq : root1Node97Domains1 = expandDomains root1Node97Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node97Domains1 v = expandDomains root1Node97Domains1Fast v from by decide) v
theorem root1Node97Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq (by decide)
theorem root1Node97Step1Narrowing_checked :
    checkNarrowing table57 root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root1Node97Domains0 root1Node97Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node97Step1Chunk0_0_checked, root1Node97Step1Chunk0_1_checked, root1Node97Step1Chunk0_2_checked, root1Node97Step1Chunk0_3_checked, root1Node97Step1Chunk0_4_checked, root1Node97Step1Chunk0_5_checked, root1Node97Step1Chunk1_0_checked, root1Node97Step1Chunk1_1_checked, root1Node97Step1Chunk1_2_checked, root1Node97Step1Chunk1_3_checked, root1Node97Step1Chunk1_4_checked, root1Node97Step1Chunk1_5_checked, root1Node97Step1Chunk2_0_checked, root1Node97Step1Chunk2_1_checked, root1Node97Step1Chunk2_2_checked, root1Node97Step1Chunk2_3_checked, root1Node97Step1Chunk2_4_checked, root1Node97Step1Chunk2_5_checked, root1Node97Step1Chunk3_0_checked, root1Node97Step1Chunk3_1_checked, root1Node97Step1Chunk3_2_checked, root1Node97Step1Chunk3_3_checked, root1Node97Step1Chunk3_4_checked, root1Node97Step1Chunk3_5_checked, root1Node97Step1Chunk4_0_checked, root1Node97Step1Chunk4_1_checked, root1Node97Step1Chunk4_2_checked, root1Node97Step1Chunk4_3_checked, root1Node97Step1Chunk4_4_checked, root1Node97Step1Chunk4_5_checked, root1Node97Step1Chunk5_0_checked, root1Node97Step1Chunk5_1_checked, root1Node97Step1Chunk5_2_checked, root1Node97Step1Chunk5_3_checked, root1Node97Step1Chunk5_4_checked, root1Node97Step1Chunk5_5_checked, root1Node97Step1Chunk6_0_checked, root1Node97Step1Chunk6_1_checked, root1Node97Step1Chunk6_2_checked, root1Node97Step1Chunk6_3_checked, root1Node97Step1Chunk6_4_checked, root1Node97Step1Chunk6_5_checked, root1Node97Step1Chunk7_0_checked, root1Node97Step1Chunk7_1_checked, root1Node97Step1Chunk7_2_checked, root1Node97Step1Chunk7_3_checked, root1Node97Step1Chunk7_4_checked, root1Node97Step1Chunk7_5_checked, root1Node97Step1Chunk8_0_checked, root1Node97Step1Chunk8_1_checked, root1Node97Step1Chunk8_2_checked, root1Node97Step1Chunk8_3_checked, root1Node97Step1Chunk8_4_checked, root1Node97Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node97Step1_checked :
    checkReplacement table57 root1Node97Domains0 root1Node97Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node97Domains0 root1Node97Domains1
    root1Node97Domains0Fast root1Node97Domains1Fast
    root1Node97Domains0_fast_eq root1Node97Domains1_fast_eq
    root1Node97Step1Narrowing_checked (by decide)
def root1Node98Domains0 : Domains 91 State := restrict root1Node97Domains1 30 (7,1)
def root1Node98Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,5),(6,2)]
  | 79 => some [(4,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(2,4),(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node98Domains0_fast_eq : root1Node98Domains0 = expandDomains root1Node98Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node98Domains0 v = expandDomains root1Node98Domains0Fast v from by decide) v
def root1Node98Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1),(4,1)]
  | 77 => [(0,2)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0),(1,3)]
  | 84 => [(3,2),(5,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(6,5)]
  | _ => [(0,4),(6,1)]
def root1Node98Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1),(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(1,3)]
  | 84 => some [(3,2),(5,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(6,5)]
  | _ => some [(0,4),(6,1)]
theorem root1Node98Domains1_fast_eq : root1Node98Domains1 = expandDomains root1Node98Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node98Domains1 v = expandDomains root1Node98Domains1Fast v from by decide) v
theorem root1Node98Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq (by decide)
theorem root1Node98Step1Narrowing_checked :
    checkNarrowing table44 root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root1Node98Domains0 root1Node98Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node98Step1Chunk0_0_checked, root1Node98Step1Chunk0_1_checked, root1Node98Step1Chunk0_2_checked, root1Node98Step1Chunk0_3_checked, root1Node98Step1Chunk0_4_checked, root1Node98Step1Chunk0_5_checked, root1Node98Step1Chunk1_0_checked, root1Node98Step1Chunk1_1_checked, root1Node98Step1Chunk1_2_checked, root1Node98Step1Chunk1_3_checked, root1Node98Step1Chunk1_4_checked, root1Node98Step1Chunk1_5_checked, root1Node98Step1Chunk2_0_checked, root1Node98Step1Chunk2_1_checked, root1Node98Step1Chunk2_2_checked, root1Node98Step1Chunk2_3_checked, root1Node98Step1Chunk2_4_checked, root1Node98Step1Chunk2_5_checked, root1Node98Step1Chunk3_0_checked, root1Node98Step1Chunk3_1_checked, root1Node98Step1Chunk3_2_checked, root1Node98Step1Chunk3_3_checked, root1Node98Step1Chunk3_4_checked, root1Node98Step1Chunk3_5_checked, root1Node98Step1Chunk4_0_checked, root1Node98Step1Chunk4_1_checked, root1Node98Step1Chunk4_2_checked, root1Node98Step1Chunk4_3_checked, root1Node98Step1Chunk4_4_checked, root1Node98Step1Chunk4_5_checked, root1Node98Step1Chunk5_0_checked, root1Node98Step1Chunk5_1_checked, root1Node98Step1Chunk5_2_checked, root1Node98Step1Chunk5_3_checked, root1Node98Step1Chunk5_4_checked, root1Node98Step1Chunk5_5_checked, root1Node98Step1Chunk6_0_checked, root1Node98Step1Chunk6_1_checked, root1Node98Step1Chunk6_2_checked, root1Node98Step1Chunk6_3_checked, root1Node98Step1Chunk6_4_checked, root1Node98Step1Chunk6_5_checked, root1Node98Step1Chunk7_0_checked, root1Node98Step1Chunk7_1_checked, root1Node98Step1Chunk7_2_checked, root1Node98Step1Chunk7_3_checked, root1Node98Step1Chunk7_4_checked, root1Node98Step1Chunk7_5_checked, root1Node98Step1Chunk8_0_checked, root1Node98Step1Chunk8_1_checked, root1Node98Step1Chunk8_2_checked, root1Node98Step1Chunk8_3_checked, root1Node98Step1Chunk8_4_checked, root1Node98Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node98Step1_checked :
    checkReplacement table44 root1Node98Domains0 root1Node98Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node98Domains0 root1Node98Domains1
    root1Node98Domains0Fast root1Node98Domains1Fast
    root1Node98Domains0_fast_eq root1Node98Domains1_fast_eq
    root1Node98Step1Narrowing_checked (by decide)
def root1Node98Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(3,1)]
  | 7 => [(0,1)]
  | 8 => [(6,2)]
  | 9 => [(8,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1)]
  | 77 => [(0,2)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0)]
  | 84 => [(3,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root1Node98Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(8,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1)]
  | 77 => some [(0,2)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0)]
  | 84 => some [(3,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root1Node98Domains2_fast_eq : root1Node98Domains2 = expandDomains root1Node98Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node98Domains2 v = expandDomains root1Node98Domains2Fast v from by decide) v
theorem root1Node98Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq (by decide)
theorem root1Node98Step2Narrowing_checked :
    checkNarrowing table56 root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root1Node98Domains1 root1Node98Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node98Step2Chunk0_0_checked, root1Node98Step2Chunk0_1_checked, root1Node98Step2Chunk0_2_checked, root1Node98Step2Chunk0_3_checked, root1Node98Step2Chunk0_4_checked, root1Node98Step2Chunk0_5_checked, root1Node98Step2Chunk1_0_checked, root1Node98Step2Chunk1_1_checked, root1Node98Step2Chunk1_2_checked, root1Node98Step2Chunk1_3_checked, root1Node98Step2Chunk1_4_checked, root1Node98Step2Chunk1_5_checked, root1Node98Step2Chunk2_0_checked, root1Node98Step2Chunk2_1_checked, root1Node98Step2Chunk2_2_checked, root1Node98Step2Chunk2_3_checked, root1Node98Step2Chunk2_4_checked, root1Node98Step2Chunk2_5_checked, root1Node98Step2Chunk3_0_checked, root1Node98Step2Chunk3_1_checked, root1Node98Step2Chunk3_2_checked, root1Node98Step2Chunk3_3_checked, root1Node98Step2Chunk3_4_checked, root1Node98Step2Chunk3_5_checked, root1Node98Step2Chunk4_0_checked, root1Node98Step2Chunk4_1_checked, root1Node98Step2Chunk4_2_checked, root1Node98Step2Chunk4_3_checked, root1Node98Step2Chunk4_4_checked, root1Node98Step2Chunk4_5_checked, root1Node98Step2Chunk5_0_checked, root1Node98Step2Chunk5_1_checked, root1Node98Step2Chunk5_2_checked, root1Node98Step2Chunk5_3_checked, root1Node98Step2Chunk5_4_checked, root1Node98Step2Chunk5_5_checked, root1Node98Step2Chunk6_0_checked, root1Node98Step2Chunk6_1_checked, root1Node98Step2Chunk6_2_checked, root1Node98Step2Chunk6_3_checked, root1Node98Step2Chunk6_4_checked, root1Node98Step2Chunk6_5_checked, root1Node98Step2Chunk7_0_checked, root1Node98Step2Chunk7_1_checked, root1Node98Step2Chunk7_2_checked, root1Node98Step2Chunk7_3_checked, root1Node98Step2Chunk7_4_checked, root1Node98Step2Chunk7_5_checked, root1Node98Step2Chunk8_0_checked, root1Node98Step2Chunk8_1_checked, root1Node98Step2Chunk8_2_checked, root1Node98Step2Chunk8_3_checked, root1Node98Step2Chunk8_4_checked, root1Node98Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node98Step2_checked :
    checkReplacement table56 root1Node98Domains1 root1Node98Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node98Domains1 root1Node98Domains2
    root1Node98Domains1Fast root1Node98Domains2Fast
    root1Node98Domains1_fast_eq root1Node98Domains2_fast_eq
    root1Node98Step2Narrowing_checked (by decide)
theorem root1Node98Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node98Domains2 (.output 48) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
