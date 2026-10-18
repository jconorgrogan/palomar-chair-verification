module

public import SpectreFinite.RadiusFiveRoot8Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable43
public import SpectreFinite.RadiusFiveTable54

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node12Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(4,3)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node12Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node12Domains2_fast_eq : root8Node12Domains2 = expandDomains root8Node12Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node12Domains2 v = expandDomains root8Node12Domains2Fast v from by decide) v
theorem root8Node12Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq (by decide)
theorem root8Node12Step2Narrowing_checked :
    checkNarrowing table54 root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node12Domains1 root8Node12Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node12Step2Chunk0_0_checked, root8Node12Step2Chunk0_1_checked, root8Node12Step2Chunk0_2_checked, root8Node12Step2Chunk0_3_checked, root8Node12Step2Chunk0_4_checked, root8Node12Step2Chunk0_5_checked, root8Node12Step2Chunk1_0_checked, root8Node12Step2Chunk1_1_checked, root8Node12Step2Chunk1_2_checked, root8Node12Step2Chunk1_3_checked, root8Node12Step2Chunk1_4_checked, root8Node12Step2Chunk1_5_checked, root8Node12Step2Chunk2_0_checked, root8Node12Step2Chunk2_1_checked, root8Node12Step2Chunk2_2_checked, root8Node12Step2Chunk2_3_checked, root8Node12Step2Chunk2_4_checked, root8Node12Step2Chunk2_5_checked, root8Node12Step2Chunk3_0_checked, root8Node12Step2Chunk3_1_checked, root8Node12Step2Chunk3_2_checked, root8Node12Step2Chunk3_3_checked, root8Node12Step2Chunk3_4_checked, root8Node12Step2Chunk3_5_checked, root8Node12Step2Chunk4_0_checked, root8Node12Step2Chunk4_1_checked, root8Node12Step2Chunk4_2_checked, root8Node12Step2Chunk4_3_checked, root8Node12Step2Chunk4_4_checked, root8Node12Step2Chunk4_5_checked, root8Node12Step2Chunk5_0_checked, root8Node12Step2Chunk5_1_checked, root8Node12Step2Chunk5_2_checked, root8Node12Step2Chunk5_3_checked, root8Node12Step2Chunk5_4_checked, root8Node12Step2Chunk5_5_checked, root8Node12Step2Chunk6_0_checked, root8Node12Step2Chunk6_1_checked, root8Node12Step2Chunk6_2_checked, root8Node12Step2Chunk6_3_checked, root8Node12Step2Chunk6_4_checked, root8Node12Step2Chunk6_5_checked, root8Node12Step2Chunk7_0_checked, root8Node12Step2Chunk7_1_checked, root8Node12Step2Chunk7_2_checked, root8Node12Step2Chunk7_3_checked, root8Node12Step2Chunk7_4_checked, root8Node12Step2Chunk7_5_checked, root8Node12Step2Chunk8_0_checked, root8Node12Step2Chunk8_1_checked, root8Node12Step2Chunk8_2_checked, root8Node12Step2Chunk8_3_checked, root8Node12Step2Chunk8_4_checked, root8Node12Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node12Step2_checked :
    checkReplacement table54 root8Node12Domains1 root8Node12Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node12Domains1 root8Node12Domains2
    root8Node12Domains1Fast root8Node12Domains2Fast
    root8Node12Domains1_fast_eq root8Node12Domains2_fast_eq
    root8Node12Step2Narrowing_checked (by decide)
theorem root8Node12Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node12Domains2 (.output 4) = true := by decide
def root8Node13Domains0 : Domains 91 State := restrict root8Node11Domains2 6 (8,1)
def root8Node13Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(1,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node13Domains0_fast_eq : root8Node13Domains0 = expandDomains root8Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node13Domains0 v = expandDomains root8Node13Domains0Fast v from by decide) v
def root8Node13Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(2,1),(2,3)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(0,0),(6,4)]
  | 41 => [(1,2),(3,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(0,3),(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node13Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node13Domains1_fast_eq : root8Node13Domains1 = expandDomains root8Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node13Domains1 v = expandDomains root8Node13Domains1Fast v from by decide) v
theorem root8Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_0⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_1⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_2⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_3⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_4⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_5⟩
      root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq (by decide)
theorem root8Node13Step1Narrowing_checked :
    checkNarrowing table43 root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkNarrowing_flatten table43Scope [table43Rows0_0,table43Rows0_1,table43Rows0_2,table43Rows0_3,table43Rows0_4,table43Rows0_5,table43Rows1_0,table43Rows1_1,table43Rows1_2,table43Rows1_3,table43Rows1_4,table43Rows1_5,table43Rows2_0,table43Rows2_1,table43Rows2_2,table43Rows2_3,table43Rows2_4,table43Rows2_5,table43Rows3_0,table43Rows3_1,table43Rows3_2,table43Rows3_3,table43Rows3_4,table43Rows3_5,table43Rows4_0,table43Rows4_1,table43Rows4_2,table43Rows4_3,table43Rows4_4,table43Rows4_5,table43Rows5_0,table43Rows5_1,table43Rows5_2,table43Rows5_3,table43Rows5_4,table43Rows5_5,table43Rows6_0,table43Rows6_1,table43Rows6_2,table43Rows6_3,table43Rows6_4,table43Rows6_5,table43Rows7_0,table43Rows7_1,table43Rows7_2,table43Rows7_3,table43Rows7_4,table43Rows7_5,table43Rows8_0,table43Rows8_1,table43Rows8_2,table43Rows8_3,table43Rows8_4,table43Rows8_5]
    root8Node13Domains0 root8Node13Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node13Step1Chunk0_0_checked, root8Node13Step1Chunk0_1_checked, root8Node13Step1Chunk0_2_checked, root8Node13Step1Chunk0_3_checked, root8Node13Step1Chunk0_4_checked, root8Node13Step1Chunk0_5_checked, root8Node13Step1Chunk1_0_checked, root8Node13Step1Chunk1_1_checked, root8Node13Step1Chunk1_2_checked, root8Node13Step1Chunk1_3_checked, root8Node13Step1Chunk1_4_checked, root8Node13Step1Chunk1_5_checked, root8Node13Step1Chunk2_0_checked, root8Node13Step1Chunk2_1_checked, root8Node13Step1Chunk2_2_checked, root8Node13Step1Chunk2_3_checked, root8Node13Step1Chunk2_4_checked, root8Node13Step1Chunk2_5_checked, root8Node13Step1Chunk3_0_checked, root8Node13Step1Chunk3_1_checked, root8Node13Step1Chunk3_2_checked, root8Node13Step1Chunk3_3_checked, root8Node13Step1Chunk3_4_checked, root8Node13Step1Chunk3_5_checked, root8Node13Step1Chunk4_0_checked, root8Node13Step1Chunk4_1_checked, root8Node13Step1Chunk4_2_checked, root8Node13Step1Chunk4_3_checked, root8Node13Step1Chunk4_4_checked, root8Node13Step1Chunk4_5_checked, root8Node13Step1Chunk5_0_checked, root8Node13Step1Chunk5_1_checked, root8Node13Step1Chunk5_2_checked, root8Node13Step1Chunk5_3_checked, root8Node13Step1Chunk5_4_checked, root8Node13Step1Chunk5_5_checked, root8Node13Step1Chunk6_0_checked, root8Node13Step1Chunk6_1_checked, root8Node13Step1Chunk6_2_checked, root8Node13Step1Chunk6_3_checked, root8Node13Step1Chunk6_4_checked, root8Node13Step1Chunk6_5_checked, root8Node13Step1Chunk7_0_checked, root8Node13Step1Chunk7_1_checked, root8Node13Step1Chunk7_2_checked, root8Node13Step1Chunk7_3_checked, root8Node13Step1Chunk7_4_checked, root8Node13Step1Chunk7_5_checked, root8Node13Step1Chunk8_0_checked, root8Node13Step1Chunk8_1_checked, root8Node13Step1Chunk8_2_checked, root8Node13Step1Chunk8_3_checked, root8Node13Step1Chunk8_4_checked, root8Node13Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node13Step1_checked :
    checkReplacement table43 root8Node13Domains0 root8Node13Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node13Domains0 root8Node13Domains1
    root8Node13Domains0Fast root8Node13Domains1Fast
    root8Node13Domains0_fast_eq root8Node13Domains1_fast_eq
    root8Node13Step1Narrowing_checked (by decide)
def root8Node13Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(2,1),(2,3)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(0,0),(6,4)]
  | 41 => [(1,2),(3,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(0,3),(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node13Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node13Domains2_fast_eq : root8Node13Domains2 = expandDomains root8Node13Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node13Domains2 v = expandDomains root8Node13Domains2Fast v from by decide) v
theorem root8Node13Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq (by decide)
theorem root8Node13Step2Narrowing_checked :
    checkNarrowing table54 root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node13Domains1 root8Node13Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node13Step2Chunk0_0_checked, root8Node13Step2Chunk0_1_checked, root8Node13Step2Chunk0_2_checked, root8Node13Step2Chunk0_3_checked, root8Node13Step2Chunk0_4_checked, root8Node13Step2Chunk0_5_checked, root8Node13Step2Chunk1_0_checked, root8Node13Step2Chunk1_1_checked, root8Node13Step2Chunk1_2_checked, root8Node13Step2Chunk1_3_checked, root8Node13Step2Chunk1_4_checked, root8Node13Step2Chunk1_5_checked, root8Node13Step2Chunk2_0_checked, root8Node13Step2Chunk2_1_checked, root8Node13Step2Chunk2_2_checked, root8Node13Step2Chunk2_3_checked, root8Node13Step2Chunk2_4_checked, root8Node13Step2Chunk2_5_checked, root8Node13Step2Chunk3_0_checked, root8Node13Step2Chunk3_1_checked, root8Node13Step2Chunk3_2_checked, root8Node13Step2Chunk3_3_checked, root8Node13Step2Chunk3_4_checked, root8Node13Step2Chunk3_5_checked, root8Node13Step2Chunk4_0_checked, root8Node13Step2Chunk4_1_checked, root8Node13Step2Chunk4_2_checked, root8Node13Step2Chunk4_3_checked, root8Node13Step2Chunk4_4_checked, root8Node13Step2Chunk4_5_checked, root8Node13Step2Chunk5_0_checked, root8Node13Step2Chunk5_1_checked, root8Node13Step2Chunk5_2_checked, root8Node13Step2Chunk5_3_checked, root8Node13Step2Chunk5_4_checked, root8Node13Step2Chunk5_5_checked, root8Node13Step2Chunk6_0_checked, root8Node13Step2Chunk6_1_checked, root8Node13Step2Chunk6_2_checked, root8Node13Step2Chunk6_3_checked, root8Node13Step2Chunk6_4_checked, root8Node13Step2Chunk6_5_checked, root8Node13Step2Chunk7_0_checked, root8Node13Step2Chunk7_1_checked, root8Node13Step2Chunk7_2_checked, root8Node13Step2Chunk7_3_checked, root8Node13Step2Chunk7_4_checked, root8Node13Step2Chunk7_5_checked, root8Node13Step2Chunk8_0_checked, root8Node13Step2Chunk8_1_checked, root8Node13Step2Chunk8_2_checked, root8Node13Step2Chunk8_3_checked, root8Node13Step2Chunk8_4_checked, root8Node13Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node13Step2_checked :
    checkReplacement table54 root8Node13Domains1 root8Node13Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node13Domains1 root8Node13Domains2
    root8Node13Domains1Fast root8Node13Domains2Fast
    root8Node13Domains1_fast_eq root8Node13Domains2_fast_eq
    root8Node13Step2Narrowing_checked (by decide)
def root8Node14Domains0 : Domains 91 State := restrict root8Node13Domains2 21 (3,4)
def root8Node14Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node14Domains0_fast_eq : root8Node14Domains0 = expandDomains root8Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node14Domains0 v = expandDomains root8Node14Domains0Fast v from by decide) v
def root8Node14Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(2,3)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(0,3)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node14Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node14Domains1_fast_eq : root8Node14Domains1 = expandDomains root8Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node14Domains1 v = expandDomains root8Node14Domains1Fast v from by decide) v
theorem root8Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq (by decide)
theorem root8Node14Step1Narrowing_checked :
    checkNarrowing table21 root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root8Node14Domains0 root8Node14Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node14Step1Chunk0_0_checked, root8Node14Step1Chunk0_1_checked, root8Node14Step1Chunk0_2_checked, root8Node14Step1Chunk0_3_checked, root8Node14Step1Chunk0_4_checked, root8Node14Step1Chunk0_5_checked, root8Node14Step1Chunk1_0_checked, root8Node14Step1Chunk1_1_checked, root8Node14Step1Chunk1_2_checked, root8Node14Step1Chunk1_3_checked, root8Node14Step1Chunk1_4_checked, root8Node14Step1Chunk1_5_checked, root8Node14Step1Chunk2_0_checked, root8Node14Step1Chunk2_1_checked, root8Node14Step1Chunk2_2_checked, root8Node14Step1Chunk2_3_checked, root8Node14Step1Chunk2_4_checked, root8Node14Step1Chunk2_5_checked, root8Node14Step1Chunk3_0_checked, root8Node14Step1Chunk3_1_checked, root8Node14Step1Chunk3_2_checked, root8Node14Step1Chunk3_3_checked, root8Node14Step1Chunk3_4_checked, root8Node14Step1Chunk3_5_checked, root8Node14Step1Chunk4_0_checked, root8Node14Step1Chunk4_1_checked, root8Node14Step1Chunk4_2_checked, root8Node14Step1Chunk4_3_checked, root8Node14Step1Chunk4_4_checked, root8Node14Step1Chunk4_5_checked, root8Node14Step1Chunk5_0_checked, root8Node14Step1Chunk5_1_checked, root8Node14Step1Chunk5_2_checked, root8Node14Step1Chunk5_3_checked, root8Node14Step1Chunk5_4_checked, root8Node14Step1Chunk5_5_checked, root8Node14Step1Chunk6_0_checked, root8Node14Step1Chunk6_1_checked, root8Node14Step1Chunk6_2_checked, root8Node14Step1Chunk6_3_checked, root8Node14Step1Chunk6_4_checked, root8Node14Step1Chunk6_5_checked, root8Node14Step1Chunk7_0_checked, root8Node14Step1Chunk7_1_checked, root8Node14Step1Chunk7_2_checked, root8Node14Step1Chunk7_3_checked, root8Node14Step1Chunk7_4_checked, root8Node14Step1Chunk7_5_checked, root8Node14Step1Chunk8_0_checked, root8Node14Step1Chunk8_1_checked, root8Node14Step1Chunk8_2_checked, root8Node14Step1Chunk8_3_checked, root8Node14Step1Chunk8_4_checked, root8Node14Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node14Step1_checked :
    checkReplacement table21 root8Node14Domains0 root8Node14Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node14Domains0 root8Node14Domains1
    root8Node14Domains0Fast root8Node14Domains1Fast
    root8Node14Domains0_fast_eq root8Node14Domains1_fast_eq
    root8Node14Step1Narrowing_checked (by decide)
theorem root8Node14Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node14Domains1 (.output 5) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
