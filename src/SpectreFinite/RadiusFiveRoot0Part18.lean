module

public import SpectreFinite.RadiusFiveRoot0Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node36Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(8,1)]
  | 29 => [(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(7,0)]
  | 40 => [(1,1),(6,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(4,1),(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(7,3),(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4),(6,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node36Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(1,1),(6,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node36Domains2_fast_eq : root0Node36Domains2 = expandDomains root0Node36Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node36Domains2 v = expandDomains root0Node36Domains2Fast v from by decide) v
theorem root0Node36Step2Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq (by decide)
theorem root0Node36Step2Narrowing_checked :
    checkNarrowing table19 root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root0Node36Domains1 root0Node36Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node36Step2Chunk0_0_checked, root0Node36Step2Chunk0_1_checked, root0Node36Step2Chunk0_2_checked, root0Node36Step2Chunk0_3_checked, root0Node36Step2Chunk0_4_checked, root0Node36Step2Chunk0_5_checked, root0Node36Step2Chunk1_0_checked, root0Node36Step2Chunk1_1_checked, root0Node36Step2Chunk1_2_checked, root0Node36Step2Chunk1_3_checked, root0Node36Step2Chunk1_4_checked, root0Node36Step2Chunk1_5_checked, root0Node36Step2Chunk2_0_checked, root0Node36Step2Chunk2_1_checked, root0Node36Step2Chunk2_2_checked, root0Node36Step2Chunk2_3_checked, root0Node36Step2Chunk2_4_checked, root0Node36Step2Chunk2_5_checked, root0Node36Step2Chunk3_0_checked, root0Node36Step2Chunk3_1_checked, root0Node36Step2Chunk3_2_checked, root0Node36Step2Chunk3_3_checked, root0Node36Step2Chunk3_4_checked, root0Node36Step2Chunk3_5_checked, root0Node36Step2Chunk4_0_checked, root0Node36Step2Chunk4_1_checked, root0Node36Step2Chunk4_2_checked, root0Node36Step2Chunk4_3_checked, root0Node36Step2Chunk4_4_checked, root0Node36Step2Chunk4_5_checked, root0Node36Step2Chunk5_0_checked, root0Node36Step2Chunk5_1_checked, root0Node36Step2Chunk5_2_checked, root0Node36Step2Chunk5_3_checked, root0Node36Step2Chunk5_4_checked, root0Node36Step2Chunk5_5_checked, root0Node36Step2Chunk6_0_checked, root0Node36Step2Chunk6_1_checked, root0Node36Step2Chunk6_2_checked, root0Node36Step2Chunk6_3_checked, root0Node36Step2Chunk6_4_checked, root0Node36Step2Chunk6_5_checked, root0Node36Step2Chunk7_0_checked, root0Node36Step2Chunk7_1_checked, root0Node36Step2Chunk7_2_checked, root0Node36Step2Chunk7_3_checked, root0Node36Step2Chunk7_4_checked, root0Node36Step2Chunk7_5_checked, root0Node36Step2Chunk8_0_checked, root0Node36Step2Chunk8_1_checked, root0Node36Step2Chunk8_2_checked, root0Node36Step2Chunk8_3_checked, root0Node36Step2Chunk8_4_checked, root0Node36Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node36Step2_checked :
    checkReplacement table19 root0Node36Domains1 root0Node36Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node36Domains1 root0Node36Domains2
    root0Node36Domains1Fast root0Node36Domains2Fast
    root0Node36Domains1_fast_eq root0Node36Domains2_fast_eq
    root0Node36Step2Narrowing_checked (by decide)
def root0Node36Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(8,1)]
  | 29 => [(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(7,0)]
  | 40 => [(1,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(4,1),(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(7,3),(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4),(6,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node36Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(1,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1),(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node36Domains3_fast_eq : root0Node36Domains3 = expandDomains root0Node36Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node36Domains3 v = expandDomains root0Node36Domains3Fast v from by decide) v
theorem root0Node36Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq (by decide)
theorem root0Node36Step3Narrowing_checked :
    checkNarrowing table6 root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root0Node36Domains2 root0Node36Domains3 (by
      simp only [List.all_cons, List.all_nil, root0Node36Step3Chunk0_0_checked, root0Node36Step3Chunk0_1_checked, root0Node36Step3Chunk0_2_checked, root0Node36Step3Chunk0_3_checked, root0Node36Step3Chunk0_4_checked, root0Node36Step3Chunk0_5_checked, root0Node36Step3Chunk1_0_checked, root0Node36Step3Chunk1_1_checked, root0Node36Step3Chunk1_2_checked, root0Node36Step3Chunk1_3_checked, root0Node36Step3Chunk1_4_checked, root0Node36Step3Chunk1_5_checked, root0Node36Step3Chunk2_0_checked, root0Node36Step3Chunk2_1_checked, root0Node36Step3Chunk2_2_checked, root0Node36Step3Chunk2_3_checked, root0Node36Step3Chunk2_4_checked, root0Node36Step3Chunk2_5_checked, root0Node36Step3Chunk3_0_checked, root0Node36Step3Chunk3_1_checked, root0Node36Step3Chunk3_2_checked, root0Node36Step3Chunk3_3_checked, root0Node36Step3Chunk3_4_checked, root0Node36Step3Chunk3_5_checked, root0Node36Step3Chunk4_0_checked, root0Node36Step3Chunk4_1_checked, root0Node36Step3Chunk4_2_checked, root0Node36Step3Chunk4_3_checked, root0Node36Step3Chunk4_4_checked, root0Node36Step3Chunk4_5_checked, root0Node36Step3Chunk5_0_checked, root0Node36Step3Chunk5_1_checked, root0Node36Step3Chunk5_2_checked, root0Node36Step3Chunk5_3_checked, root0Node36Step3Chunk5_4_checked, root0Node36Step3Chunk5_5_checked, root0Node36Step3Chunk6_0_checked, root0Node36Step3Chunk6_1_checked, root0Node36Step3Chunk6_2_checked, root0Node36Step3Chunk6_3_checked, root0Node36Step3Chunk6_4_checked, root0Node36Step3Chunk6_5_checked, root0Node36Step3Chunk7_0_checked, root0Node36Step3Chunk7_1_checked, root0Node36Step3Chunk7_2_checked, root0Node36Step3Chunk7_3_checked, root0Node36Step3Chunk7_4_checked, root0Node36Step3Chunk7_5_checked, root0Node36Step3Chunk8_0_checked, root0Node36Step3Chunk8_1_checked, root0Node36Step3Chunk8_2_checked, root0Node36Step3Chunk8_3_checked, root0Node36Step3Chunk8_4_checked, root0Node36Step3Chunk8_5_checked, Bool.true_and])
theorem root0Node36Step3_checked :
    checkReplacement table6 root0Node36Domains2 root0Node36Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root0Node36Domains2 root0Node36Domains3
    root0Node36Domains2Fast root0Node36Domains3Fast
    root0Node36Domains2_fast_eq root0Node36Domains3_fast_eq
    root0Node36Step3Narrowing_checked (by decide)
def root0Node37Domains0 : Domains 91 State := restrict root0Node36Domains3 60 (4,1)
def root0Node37Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(1,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node37Domains0_fast_eq : root0Node37Domains0 = expandDomains root0Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node37Domains0 v = expandDomains root0Node37Domains0Fast v from by decide) v
def root0Node37Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(8,1)]
  | 29 => [(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(7,0)]
  | 40 => [(1,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(4,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(7,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(6,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node37Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(1,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(4,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node37Domains1_fast_eq : root0Node37Domains1 = expandDomains root0Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node37Domains1 v = expandDomains root0Node37Domains1Fast v from by decide) v
theorem root0Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq (by decide)
theorem root0Node37Step1Narrowing_checked :
    checkNarrowing table36 root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root0Node37Domains0 root0Node37Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node37Step1Chunk0_0_checked, root0Node37Step1Chunk0_1_checked, root0Node37Step1Chunk0_2_checked, root0Node37Step1Chunk0_3_checked, root0Node37Step1Chunk0_4_checked, root0Node37Step1Chunk0_5_checked, root0Node37Step1Chunk1_0_checked, root0Node37Step1Chunk1_1_checked, root0Node37Step1Chunk1_2_checked, root0Node37Step1Chunk1_3_checked, root0Node37Step1Chunk1_4_checked, root0Node37Step1Chunk1_5_checked, root0Node37Step1Chunk2_0_checked, root0Node37Step1Chunk2_1_checked, root0Node37Step1Chunk2_2_checked, root0Node37Step1Chunk2_3_checked, root0Node37Step1Chunk2_4_checked, root0Node37Step1Chunk2_5_checked, root0Node37Step1Chunk3_0_checked, root0Node37Step1Chunk3_1_checked, root0Node37Step1Chunk3_2_checked, root0Node37Step1Chunk3_3_checked, root0Node37Step1Chunk3_4_checked, root0Node37Step1Chunk3_5_checked, root0Node37Step1Chunk4_0_checked, root0Node37Step1Chunk4_1_checked, root0Node37Step1Chunk4_2_checked, root0Node37Step1Chunk4_3_checked, root0Node37Step1Chunk4_4_checked, root0Node37Step1Chunk4_5_checked, root0Node37Step1Chunk5_0_checked, root0Node37Step1Chunk5_1_checked, root0Node37Step1Chunk5_2_checked, root0Node37Step1Chunk5_3_checked, root0Node37Step1Chunk5_4_checked, root0Node37Step1Chunk5_5_checked, root0Node37Step1Chunk6_0_checked, root0Node37Step1Chunk6_1_checked, root0Node37Step1Chunk6_2_checked, root0Node37Step1Chunk6_3_checked, root0Node37Step1Chunk6_4_checked, root0Node37Step1Chunk6_5_checked, root0Node37Step1Chunk7_0_checked, root0Node37Step1Chunk7_1_checked, root0Node37Step1Chunk7_2_checked, root0Node37Step1Chunk7_3_checked, root0Node37Step1Chunk7_4_checked, root0Node37Step1Chunk7_5_checked, root0Node37Step1Chunk8_0_checked, root0Node37Step1Chunk8_1_checked, root0Node37Step1Chunk8_2_checked, root0Node37Step1Chunk8_3_checked, root0Node37Step1Chunk8_4_checked, root0Node37Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node37Step1_checked :
    checkReplacement table36 root0Node37Domains0 root0Node37Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node37Domains0 root0Node37Domains1
    root0Node37Domains0Fast root0Node37Domains1Fast
    root0Node37Domains0_fast_eq root0Node37Domains1_fast_eq
    root0Node37Step1Narrowing_checked (by decide)
theorem root0Node37Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node37Domains1 (.output 17) = true := by decide
def root0Node38Domains0 : Domains 91 State := restrict root0Node36Domains3 60 (8,1)
def root0Node38Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(1,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(7,3),(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4),(6,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node38Domains0_fast_eq : root0Node38Domains0 = expandDomains root0Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node38Domains0 v = expandDomains root0Node38Domains0Fast v from by decide) v
def root0Node38Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(4,0)]
  | 8 => [(7,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(6,1)]
  | 14 => [(5,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(8,5)]
  | 24 => [(1,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(8,1)]
  | 29 => [(6,5)]
  | 30 => [(7,2)]
  | 31 => [(7,4)]
  | 32 => [(1,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(7,0)]
  | 40 => [(1,1)]
  | 41 => [(8,1)]
  | 42 => [(6,5)]
  | 43 => [(0,4)]
  | 44 => [(5,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(6,3)]
  | 49 => [(7,2)]
  | 50 => [(7,4)]
  | 51 => [(8,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(4,3)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1)]
  | 58 => [(0,2)]
  | 59 => [(1,1)]
  | 60 => [(8,1)]
  | 61 => [(0,5)]
  | 62 => [(4,4)]
  | 63 => [(1,4)]
  | 64 => [(0,5)]
  | 65 => [(2,0)]
  | 66 => [(7,3)]
  | 67 => [(5,2)]
  | 68 => [(8,0)]
  | 69 => [(8,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(6,0)]
  | 73 => [(3,1)]
  | 74 => [(0,1)]
  | 75 => [(6,2)]
  | 76 => [(8,4)]
  | 77 => [(1,4)]
  | 78 => [(7,3)]
  | 79 => [(8,2)]
  | 80 => [(5,0)]
  | 81 => [(4,5)]
  | 82 => [(1,0)]
  | 83 => [(7,1)]
  | 84 => [(7,5)]
  | 85 => [(1,2)]
  | 86 => [(8,4)]
  | 87 => [(0,0)]
  | 88 => [(7,2)]
  | 89 => [(4,0)]
  | _ => [(7,3)]
def root0Node38Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(4,0)]
  | 8 => some [(7,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(6,1)]
  | 14 => some [(5,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(8,5)]
  | 24 => some [(1,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(8,1)]
  | 29 => some [(6,5)]
  | 30 => some [(7,2)]
  | 31 => some [(7,4)]
  | 32 => some [(1,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(7,0)]
  | 40 => some [(1,1)]
  | 41 => some [(8,1)]
  | 42 => some [(6,5)]
  | 43 => some [(0,4)]
  | 44 => some [(5,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(6,3)]
  | 49 => some [(7,2)]
  | 50 => some [(7,4)]
  | 51 => some [(8,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(4,3)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1)]
  | 58 => some [(0,2)]
  | 59 => some [(1,1)]
  | 60 => some [(8,1)]
  | 61 => some [(0,5)]
  | 62 => some [(4,4)]
  | 63 => some [(1,4)]
  | 64 => some [(0,5)]
  | 65 => some [(2,0)]
  | 66 => some [(7,3)]
  | 67 => some [(5,2)]
  | 68 => some [(8,0)]
  | 69 => some [(8,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(6,0)]
  | 73 => some [(3,1)]
  | 74 => some [(0,1)]
  | 75 => some [(6,2)]
  | 76 => some [(8,4)]
  | 77 => some [(1,4)]
  | 78 => some [(7,3)]
  | 79 => some [(8,2)]
  | 80 => some [(5,0)]
  | 81 => some [(4,5)]
  | 82 => some [(1,0)]
  | 83 => some [(7,1)]
  | 84 => some [(7,5)]
  | 85 => some [(1,2)]
  | 86 => some [(8,4)]
  | 87 => some [(0,0)]
  | 88 => some [(7,2)]
  | 89 => some [(4,0)]
  | _ => some [(7,3)]
theorem root0Node38Domains1_fast_eq : root0Node38Domains1 = expandDomains root0Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node38Domains1 v = expandDomains root0Node38Domains1Fast v from by decide) v
theorem root0Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Narrowing_checked :
    checkNarrowing table36 root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root0Node38Domains0 root0Node38Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node38Step1Chunk0_0_checked, root0Node38Step1Chunk0_1_checked, root0Node38Step1Chunk0_2_checked, root0Node38Step1Chunk0_3_checked, root0Node38Step1Chunk0_4_checked, root0Node38Step1Chunk0_5_checked, root0Node38Step1Chunk1_0_checked, root0Node38Step1Chunk1_1_checked, root0Node38Step1Chunk1_2_checked, root0Node38Step1Chunk1_3_checked, root0Node38Step1Chunk1_4_checked, root0Node38Step1Chunk1_5_checked, root0Node38Step1Chunk2_0_checked, root0Node38Step1Chunk2_1_checked, root0Node38Step1Chunk2_2_checked, root0Node38Step1Chunk2_3_checked, root0Node38Step1Chunk2_4_checked, root0Node38Step1Chunk2_5_checked, root0Node38Step1Chunk3_0_checked, root0Node38Step1Chunk3_1_checked, root0Node38Step1Chunk3_2_checked, root0Node38Step1Chunk3_3_checked, root0Node38Step1Chunk3_4_checked, root0Node38Step1Chunk3_5_checked, root0Node38Step1Chunk4_0_checked, root0Node38Step1Chunk4_1_checked, root0Node38Step1Chunk4_2_checked, root0Node38Step1Chunk4_3_checked, root0Node38Step1Chunk4_4_checked, root0Node38Step1Chunk4_5_checked, root0Node38Step1Chunk5_0_checked, root0Node38Step1Chunk5_1_checked, root0Node38Step1Chunk5_2_checked, root0Node38Step1Chunk5_3_checked, root0Node38Step1Chunk5_4_checked, root0Node38Step1Chunk5_5_checked, root0Node38Step1Chunk6_0_checked, root0Node38Step1Chunk6_1_checked, root0Node38Step1Chunk6_2_checked, root0Node38Step1Chunk6_3_checked, root0Node38Step1Chunk6_4_checked, root0Node38Step1Chunk6_5_checked, root0Node38Step1Chunk7_0_checked, root0Node38Step1Chunk7_1_checked, root0Node38Step1Chunk7_2_checked, root0Node38Step1Chunk7_3_checked, root0Node38Step1Chunk7_4_checked, root0Node38Step1Chunk7_5_checked, root0Node38Step1Chunk8_0_checked, root0Node38Step1Chunk8_1_checked, root0Node38Step1Chunk8_2_checked, root0Node38Step1Chunk8_3_checked, root0Node38Step1Chunk8_4_checked, root0Node38Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node38Step1_checked :
    checkReplacement table36 root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq
    root0Node38Step1Narrowing_checked (by decide)
theorem root0Node38Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node38Domains1 (.output 18) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
