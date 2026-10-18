module

public import SpectreFinite.RadiusFiveRoot7Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node34Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(2,4)]
  | 4 => [(1,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(1,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(7,5)]
  | 51 => [(6,5)]
  | 52 => [(0,4)]
  | 53 => [(3,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | 60 => [(1,3),(6,3)]
  | 61 => [(7,0)]
  | 62 => [(2,3)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(4,1),(8,1)]
  | 69 => [(0,2),(6,5)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3),(8,3)]
  | 77 => [(5,2),(5,5)]
  | 78 => [(0,3)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(1,4),(6,4)]
  | 84 => [(0,5),(1,2)]
  | 85 => [(5,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3),(6,0)]
def root7Node34Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(3,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3),(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(2,3)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(0,3)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node34Domains2_fast_eq : root7Node34Domains2 = expandDomains root7Node34Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node34Domains2 v = expandDomains root7Node34Domains2Fast v from by decide) v
theorem root7Node34Step2Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq (by decide)
theorem root7Node34Step2Narrowing_checked :
    checkNarrowing table19 root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root7Node34Domains1 root7Node34Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node34Step2Chunk0_0_checked, root7Node34Step2Chunk0_1_checked, root7Node34Step2Chunk0_2_checked, root7Node34Step2Chunk0_3_checked, root7Node34Step2Chunk0_4_checked, root7Node34Step2Chunk0_5_checked, root7Node34Step2Chunk1_0_checked, root7Node34Step2Chunk1_1_checked, root7Node34Step2Chunk1_2_checked, root7Node34Step2Chunk1_3_checked, root7Node34Step2Chunk1_4_checked, root7Node34Step2Chunk1_5_checked, root7Node34Step2Chunk2_0_checked, root7Node34Step2Chunk2_1_checked, root7Node34Step2Chunk2_2_checked, root7Node34Step2Chunk2_3_checked, root7Node34Step2Chunk2_4_checked, root7Node34Step2Chunk2_5_checked, root7Node34Step2Chunk3_0_checked, root7Node34Step2Chunk3_1_checked, root7Node34Step2Chunk3_2_checked, root7Node34Step2Chunk3_3_checked, root7Node34Step2Chunk3_4_checked, root7Node34Step2Chunk3_5_checked, root7Node34Step2Chunk4_0_checked, root7Node34Step2Chunk4_1_checked, root7Node34Step2Chunk4_2_checked, root7Node34Step2Chunk4_3_checked, root7Node34Step2Chunk4_4_checked, root7Node34Step2Chunk4_5_checked, root7Node34Step2Chunk5_0_checked, root7Node34Step2Chunk5_1_checked, root7Node34Step2Chunk5_2_checked, root7Node34Step2Chunk5_3_checked, root7Node34Step2Chunk5_4_checked, root7Node34Step2Chunk5_5_checked, root7Node34Step2Chunk6_0_checked, root7Node34Step2Chunk6_1_checked, root7Node34Step2Chunk6_2_checked, root7Node34Step2Chunk6_3_checked, root7Node34Step2Chunk6_4_checked, root7Node34Step2Chunk6_5_checked, root7Node34Step2Chunk7_0_checked, root7Node34Step2Chunk7_1_checked, root7Node34Step2Chunk7_2_checked, root7Node34Step2Chunk7_3_checked, root7Node34Step2Chunk7_4_checked, root7Node34Step2Chunk7_5_checked, root7Node34Step2Chunk8_0_checked, root7Node34Step2Chunk8_1_checked, root7Node34Step2Chunk8_2_checked, root7Node34Step2Chunk8_3_checked, root7Node34Step2Chunk8_4_checked, root7Node34Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node34Step2_checked :
    checkReplacement table19 root7Node34Domains1 root7Node34Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node34Domains1 root7Node34Domains2
    root7Node34Domains1Fast root7Node34Domains2Fast
    root7Node34Domains1_fast_eq root7Node34Domains2_fast_eq
    root7Node34Step2Narrowing_checked (by decide)
def root7Node35Domains0 : Domains 91 State := restrict root7Node34Domains2 60 (1,3)
def root7Node35Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(3,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3)]
  | 61 => some [(7,0)]
  | 62 => some [(2,3)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(0,3)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node35Domains0_fast_eq : root7Node35Domains0 = expandDomains root7Node35Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node35Domains0 v = expandDomains root7Node35Domains0Fast v from by decide) v
def root7Node35Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(2,4)]
  | 4 => [(1,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(1,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(7,5)]
  | 51 => [(6,5)]
  | 52 => [(0,4)]
  | 53 => [(3,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | 60 => [(1,3)]
  | 61 => [(7,0)]
  | 62 => [(2,3)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(8,1)]
  | 69 => [(6,5)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(8,3)]
  | 77 => [(5,5)]
  | 78 => [(0,3)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(5,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node35Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(3,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3)]
  | 61 => some [(7,0)]
  | 62 => some [(2,3)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(8,1)]
  | 69 => some [(6,5)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(8,3)]
  | 77 => some [(5,5)]
  | 78 => some [(0,3)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node35Domains1_fast_eq : root7Node35Domains1 = expandDomains root7Node35Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node35Domains1 v = expandDomains root7Node35Domains1Fast v from by decide) v
theorem root7Node35Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq (by decide)
theorem root7Node35Step1Narrowing_checked :
    checkNarrowing table56 root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node35Domains0 root7Node35Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node35Step1Chunk0_0_checked, root7Node35Step1Chunk0_1_checked, root7Node35Step1Chunk0_2_checked, root7Node35Step1Chunk0_3_checked, root7Node35Step1Chunk0_4_checked, root7Node35Step1Chunk0_5_checked, root7Node35Step1Chunk1_0_checked, root7Node35Step1Chunk1_1_checked, root7Node35Step1Chunk1_2_checked, root7Node35Step1Chunk1_3_checked, root7Node35Step1Chunk1_4_checked, root7Node35Step1Chunk1_5_checked, root7Node35Step1Chunk2_0_checked, root7Node35Step1Chunk2_1_checked, root7Node35Step1Chunk2_2_checked, root7Node35Step1Chunk2_3_checked, root7Node35Step1Chunk2_4_checked, root7Node35Step1Chunk2_5_checked, root7Node35Step1Chunk3_0_checked, root7Node35Step1Chunk3_1_checked, root7Node35Step1Chunk3_2_checked, root7Node35Step1Chunk3_3_checked, root7Node35Step1Chunk3_4_checked, root7Node35Step1Chunk3_5_checked, root7Node35Step1Chunk4_0_checked, root7Node35Step1Chunk4_1_checked, root7Node35Step1Chunk4_2_checked, root7Node35Step1Chunk4_3_checked, root7Node35Step1Chunk4_4_checked, root7Node35Step1Chunk4_5_checked, root7Node35Step1Chunk5_0_checked, root7Node35Step1Chunk5_1_checked, root7Node35Step1Chunk5_2_checked, root7Node35Step1Chunk5_3_checked, root7Node35Step1Chunk5_4_checked, root7Node35Step1Chunk5_5_checked, root7Node35Step1Chunk6_0_checked, root7Node35Step1Chunk6_1_checked, root7Node35Step1Chunk6_2_checked, root7Node35Step1Chunk6_3_checked, root7Node35Step1Chunk6_4_checked, root7Node35Step1Chunk6_5_checked, root7Node35Step1Chunk7_0_checked, root7Node35Step1Chunk7_1_checked, root7Node35Step1Chunk7_2_checked, root7Node35Step1Chunk7_3_checked, root7Node35Step1Chunk7_4_checked, root7Node35Step1Chunk7_5_checked, root7Node35Step1Chunk8_0_checked, root7Node35Step1Chunk8_1_checked, root7Node35Step1Chunk8_2_checked, root7Node35Step1Chunk8_3_checked, root7Node35Step1Chunk8_4_checked, root7Node35Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node35Step1_checked :
    checkReplacement table56 root7Node35Domains0 root7Node35Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node35Domains0 root7Node35Domains1
    root7Node35Domains0Fast root7Node35Domains1Fast
    root7Node35Domains0_fast_eq root7Node35Domains1_fast_eq
    root7Node35Step1Narrowing_checked (by decide)
theorem root7Node35Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node35Domains1 (.output 14) = true := by decide
def root7Node36Domains0 : Domains 91 State := restrict root7Node34Domains2 60 (6,3)
def root7Node36Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(3,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(2,3)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(0,3)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node36Domains0_fast_eq : root7Node36Domains0 = expandDomains root7Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node36Domains0 v = expandDomains root7Node36Domains0Fast v from by decide) v
def root7Node36Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(2,4)]
  | 4 => [(1,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(1,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(7,5)]
  | 51 => [(6,5)]
  | 52 => [(0,4)]
  | 53 => [(3,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | 60 => [(6,3)]
  | 61 => [(7,0)]
  | 62 => [(2,3)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(4,1)]
  | 69 => [(0,2)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(5,2)]
  | 78 => [(0,3)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(5,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root7Node36Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(3,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(2,3)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1)]
  | 69 => some [(0,2)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(5,2)]
  | 78 => some [(0,3)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root7Node36Domains1_fast_eq : root7Node36Domains1 = expandDomains root7Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node36Domains1 v = expandDomains root7Node36Domains1Fast v from by decide) v
theorem root7Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Narrowing_checked :
    checkNarrowing table56 root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node36Domains0 root7Node36Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node36Step1Chunk0_0_checked, root7Node36Step1Chunk0_1_checked, root7Node36Step1Chunk0_2_checked, root7Node36Step1Chunk0_3_checked, root7Node36Step1Chunk0_4_checked, root7Node36Step1Chunk0_5_checked, root7Node36Step1Chunk1_0_checked, root7Node36Step1Chunk1_1_checked, root7Node36Step1Chunk1_2_checked, root7Node36Step1Chunk1_3_checked, root7Node36Step1Chunk1_4_checked, root7Node36Step1Chunk1_5_checked, root7Node36Step1Chunk2_0_checked, root7Node36Step1Chunk2_1_checked, root7Node36Step1Chunk2_2_checked, root7Node36Step1Chunk2_3_checked, root7Node36Step1Chunk2_4_checked, root7Node36Step1Chunk2_5_checked, root7Node36Step1Chunk3_0_checked, root7Node36Step1Chunk3_1_checked, root7Node36Step1Chunk3_2_checked, root7Node36Step1Chunk3_3_checked, root7Node36Step1Chunk3_4_checked, root7Node36Step1Chunk3_5_checked, root7Node36Step1Chunk4_0_checked, root7Node36Step1Chunk4_1_checked, root7Node36Step1Chunk4_2_checked, root7Node36Step1Chunk4_3_checked, root7Node36Step1Chunk4_4_checked, root7Node36Step1Chunk4_5_checked, root7Node36Step1Chunk5_0_checked, root7Node36Step1Chunk5_1_checked, root7Node36Step1Chunk5_2_checked, root7Node36Step1Chunk5_3_checked, root7Node36Step1Chunk5_4_checked, root7Node36Step1Chunk5_5_checked, root7Node36Step1Chunk6_0_checked, root7Node36Step1Chunk6_1_checked, root7Node36Step1Chunk6_2_checked, root7Node36Step1Chunk6_3_checked, root7Node36Step1Chunk6_4_checked, root7Node36Step1Chunk6_5_checked, root7Node36Step1Chunk7_0_checked, root7Node36Step1Chunk7_1_checked, root7Node36Step1Chunk7_2_checked, root7Node36Step1Chunk7_3_checked, root7Node36Step1Chunk7_4_checked, root7Node36Step1Chunk7_5_checked, root7Node36Step1Chunk8_0_checked, root7Node36Step1Chunk8_1_checked, root7Node36Step1Chunk8_2_checked, root7Node36Step1Chunk8_3_checked, root7Node36Step1Chunk8_4_checked, root7Node36Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node36Step1_checked :
    checkReplacement table56 root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq
    root7Node36Step1Narrowing_checked (by decide)
theorem root7Node36Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node36Domains1 (.output 15) = true := by decide
def root7Node37Domains0 : Domains 91 State := restrict root7Node25Domains1 21 (8,4)
def root7Node37Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(4,3),(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(1,4),(3,4),(5,4)]
  | 40 => some [(4,0),(7,4)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5),(8,5)]
  | 48 => some [(3,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,3)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1),(6,5)]
  | 52 => some [(0,4),(6,2)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(0,0),(1,4),(6,4),(7,4)]
  | 60 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 61 => some [(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5)]
  | 66 => some [(0,2),(6,0)]
  | 67 => some [(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(7,5),(8,1)]
  | 69 => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(3,2),(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2),(8,2)]
  | 75 => some [(5,0),(8,0)]
  | 76 => some [(4,5),(7,3),(8,3)]
  | 77 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => some [(0,3),(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0),(1,4),(6,4)]
  | 84 => some [(0,5),(1,2),(7,2)]
  | 85 => some [(5,3),(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,0),(6,1)]
theorem root7Node37Domains0_fast_eq : root7Node37Domains0 = expandDomains root7Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node37Domains0 v = expandDomains root7Node37Domains0Fast v from by decide) v
def root7Node37Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(2,4)]
  | 4 => [(1,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(4,2),(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(1,4),(3,4),(5,4)]
  | 40 => [(4,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(2,3),(2,5),(4,3)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1)]
  | 52 => [(6,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(0,0),(1,4),(6,4),(7,4)]
  | 60 => [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 61 => [(1,0)]
  | 62 => [(2,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(1,5),(4,1),(7,5),(8,1)]
  | 69 => [(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 70 => [(0,0)]
  | 71 => [(3,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(4,5),(7,3),(8,3)]
  | 77 => [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0),(1,4),(6,4)]
  | 84 => [(0,5),(1,2),(7,2)]
  | 85 => [(5,3),(8,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,0),(6,1)]
def root7Node37Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,4)]
  | 4 => some [(1,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(1,4),(3,4),(5,4)]
  | 40 => some [(4,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(2,3),(2,5),(4,3)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1)]
  | 52 => some [(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(0,0),(1,4),(6,4),(7,4)]
  | 60 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 61 => some [(1,0)]
  | 62 => some [(2,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(1,5),(4,1),(7,5),(8,1)]
  | 69 => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 70 => some [(0,0)]
  | 71 => some [(3,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(4,5),(7,3),(8,3)]
  | 77 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0),(1,4),(6,4)]
  | 84 => some [(0,5),(1,2),(7,2)]
  | 85 => some [(5,3),(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,0),(6,1)]
theorem root7Node37Domains1_fast_eq : root7Node37Domains1 = expandDomains root7Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node37Domains1 v = expandDomains root7Node37Domains1Fast v from by decide) v
theorem root7Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Narrowing_checked :
    checkNarrowing table44 root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root7Node37Domains0 root7Node37Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node37Step1Chunk0_0_checked, root7Node37Step1Chunk0_1_checked, root7Node37Step1Chunk0_2_checked, root7Node37Step1Chunk0_3_checked, root7Node37Step1Chunk0_4_checked, root7Node37Step1Chunk0_5_checked, root7Node37Step1Chunk1_0_checked, root7Node37Step1Chunk1_1_checked, root7Node37Step1Chunk1_2_checked, root7Node37Step1Chunk1_3_checked, root7Node37Step1Chunk1_4_checked, root7Node37Step1Chunk1_5_checked, root7Node37Step1Chunk2_0_checked, root7Node37Step1Chunk2_1_checked, root7Node37Step1Chunk2_2_checked, root7Node37Step1Chunk2_3_checked, root7Node37Step1Chunk2_4_checked, root7Node37Step1Chunk2_5_checked, root7Node37Step1Chunk3_0_checked, root7Node37Step1Chunk3_1_checked, root7Node37Step1Chunk3_2_checked, root7Node37Step1Chunk3_3_checked, root7Node37Step1Chunk3_4_checked, root7Node37Step1Chunk3_5_checked, root7Node37Step1Chunk4_0_checked, root7Node37Step1Chunk4_1_checked, root7Node37Step1Chunk4_2_checked, root7Node37Step1Chunk4_3_checked, root7Node37Step1Chunk4_4_checked, root7Node37Step1Chunk4_5_checked, root7Node37Step1Chunk5_0_checked, root7Node37Step1Chunk5_1_checked, root7Node37Step1Chunk5_2_checked, root7Node37Step1Chunk5_3_checked, root7Node37Step1Chunk5_4_checked, root7Node37Step1Chunk5_5_checked, root7Node37Step1Chunk6_0_checked, root7Node37Step1Chunk6_1_checked, root7Node37Step1Chunk6_2_checked, root7Node37Step1Chunk6_3_checked, root7Node37Step1Chunk6_4_checked, root7Node37Step1Chunk6_5_checked, root7Node37Step1Chunk7_0_checked, root7Node37Step1Chunk7_1_checked, root7Node37Step1Chunk7_2_checked, root7Node37Step1Chunk7_3_checked, root7Node37Step1Chunk7_4_checked, root7Node37Step1Chunk7_5_checked, root7Node37Step1Chunk8_0_checked, root7Node37Step1Chunk8_1_checked, root7Node37Step1Chunk8_2_checked, root7Node37Step1Chunk8_3_checked, root7Node37Step1Chunk8_4_checked, root7Node37Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node37Step1_checked :
    checkReplacement table44 root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq
    root7Node37Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
