module

public import SpectreFinite.RadiusFiveRoot0Part30
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable27
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node71Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(8,3)]
  | 9 => [(5,5)]
  | 10 => [(1,0)]
  | 11 => [(2,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1)]
  | 29 => [(0,1)]
  | 30 => [(7,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0)]
  | 40 => [(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2)]
  | 77 => [(7,4)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(1,1)]
  | 84 => [(4,1),(8,1)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(8,0)]
  | _ => [(7,3),(8,3)]
def root0Node71Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0)]
  | 11 => some [(2,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(4,1),(8,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node71Domains2_fast_eq : root0Node71Domains2 = expandDomains root0Node71Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node71Domains2 v = expandDomains root0Node71Domains2Fast v from by decide) v
theorem root0Node71Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq (by decide)
theorem root0Node71Step2Narrowing_checked :
    checkNarrowing table65 root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root0Node71Domains1 root0Node71Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node71Step2Chunk0_0_checked, root0Node71Step2Chunk0_1_checked, root0Node71Step2Chunk0_2_checked, root0Node71Step2Chunk0_3_checked, root0Node71Step2Chunk0_4_checked, root0Node71Step2Chunk0_5_checked, root0Node71Step2Chunk1_0_checked, root0Node71Step2Chunk1_1_checked, root0Node71Step2Chunk1_2_checked, root0Node71Step2Chunk1_3_checked, root0Node71Step2Chunk1_4_checked, root0Node71Step2Chunk1_5_checked, root0Node71Step2Chunk2_0_checked, root0Node71Step2Chunk2_1_checked, root0Node71Step2Chunk2_2_checked, root0Node71Step2Chunk2_3_checked, root0Node71Step2Chunk2_4_checked, root0Node71Step2Chunk2_5_checked, root0Node71Step2Chunk3_0_checked, root0Node71Step2Chunk3_1_checked, root0Node71Step2Chunk3_2_checked, root0Node71Step2Chunk3_3_checked, root0Node71Step2Chunk3_4_checked, root0Node71Step2Chunk3_5_checked, root0Node71Step2Chunk4_0_checked, root0Node71Step2Chunk4_1_checked, root0Node71Step2Chunk4_2_checked, root0Node71Step2Chunk4_3_checked, root0Node71Step2Chunk4_4_checked, root0Node71Step2Chunk4_5_checked, root0Node71Step2Chunk5_0_checked, root0Node71Step2Chunk5_1_checked, root0Node71Step2Chunk5_2_checked, root0Node71Step2Chunk5_3_checked, root0Node71Step2Chunk5_4_checked, root0Node71Step2Chunk5_5_checked, root0Node71Step2Chunk6_0_checked, root0Node71Step2Chunk6_1_checked, root0Node71Step2Chunk6_2_checked, root0Node71Step2Chunk6_3_checked, root0Node71Step2Chunk6_4_checked, root0Node71Step2Chunk6_5_checked, root0Node71Step2Chunk7_0_checked, root0Node71Step2Chunk7_1_checked, root0Node71Step2Chunk7_2_checked, root0Node71Step2Chunk7_3_checked, root0Node71Step2Chunk7_4_checked, root0Node71Step2Chunk7_5_checked, root0Node71Step2Chunk8_0_checked, root0Node71Step2Chunk8_1_checked, root0Node71Step2Chunk8_2_checked, root0Node71Step2Chunk8_3_checked, root0Node71Step2Chunk8_4_checked, root0Node71Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node71Step2_checked :
    checkReplacement table65 root0Node71Domains1 root0Node71Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node71Domains1 root0Node71Domains2
    root0Node71Domains1Fast root0Node71Domains2Fast
    root0Node71Domains1_fast_eq root0Node71Domains2_fast_eq
    root0Node71Step2Narrowing_checked (by decide)
def root0Node71Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(8,3)]
  | 9 => [(5,5)]
  | 10 => [(1,0)]
  | 11 => [(2,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1)]
  | 29 => [(0,1)]
  | 30 => [(7,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0)]
  | 40 => [(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2)]
  | 77 => [(7,4)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(1,1)]
  | 84 => [(4,1),(8,1)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(8,0)]
  | _ => [(7,3),(8,3)]
def root0Node71Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0)]
  | 11 => some [(2,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(4,1),(8,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node71Domains3_fast_eq : root0Node71Domains3 = expandDomains root0Node71Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node71Domains3 v = expandDomains root0Node71Domains3Fast v from by decide) v
theorem root0Node71Step3Chunk0_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk0_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk0_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk0_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk0_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk0_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk1_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk1_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk1_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk1_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk1_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk1_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk2_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk2_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk2_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk2_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk2_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk2_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk3_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk3_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk3_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk3_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk3_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk3_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk4_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk4_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk4_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk4_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk4_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk4_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk5_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk5_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk5_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk5_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk5_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk5_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk6_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk6_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk6_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk6_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk6_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk6_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk7_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk7_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk7_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk7_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk7_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk7_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk8_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_0⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk8_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_1⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk8_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_2⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk8_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_3⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk8_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_4⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Chunk8_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_5⟩
      root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq (by decide)
theorem root0Node71Step3Narrowing_checked :
    checkNarrowing table27 root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkNarrowing_flatten table27Scope [table27Rows0_0,table27Rows0_1,table27Rows0_2,table27Rows0_3,table27Rows0_4,table27Rows0_5,table27Rows1_0,table27Rows1_1,table27Rows1_2,table27Rows1_3,table27Rows1_4,table27Rows1_5,table27Rows2_0,table27Rows2_1,table27Rows2_2,table27Rows2_3,table27Rows2_4,table27Rows2_5,table27Rows3_0,table27Rows3_1,table27Rows3_2,table27Rows3_3,table27Rows3_4,table27Rows3_5,table27Rows4_0,table27Rows4_1,table27Rows4_2,table27Rows4_3,table27Rows4_4,table27Rows4_5,table27Rows5_0,table27Rows5_1,table27Rows5_2,table27Rows5_3,table27Rows5_4,table27Rows5_5,table27Rows6_0,table27Rows6_1,table27Rows6_2,table27Rows6_3,table27Rows6_4,table27Rows6_5,table27Rows7_0,table27Rows7_1,table27Rows7_2,table27Rows7_3,table27Rows7_4,table27Rows7_5,table27Rows8_0,table27Rows8_1,table27Rows8_2,table27Rows8_3,table27Rows8_4,table27Rows8_5]
    root0Node71Domains2 root0Node71Domains3 (by
      simp only [List.all_cons, List.all_nil, root0Node71Step3Chunk0_0_checked, root0Node71Step3Chunk0_1_checked, root0Node71Step3Chunk0_2_checked, root0Node71Step3Chunk0_3_checked, root0Node71Step3Chunk0_4_checked, root0Node71Step3Chunk0_5_checked, root0Node71Step3Chunk1_0_checked, root0Node71Step3Chunk1_1_checked, root0Node71Step3Chunk1_2_checked, root0Node71Step3Chunk1_3_checked, root0Node71Step3Chunk1_4_checked, root0Node71Step3Chunk1_5_checked, root0Node71Step3Chunk2_0_checked, root0Node71Step3Chunk2_1_checked, root0Node71Step3Chunk2_2_checked, root0Node71Step3Chunk2_3_checked, root0Node71Step3Chunk2_4_checked, root0Node71Step3Chunk2_5_checked, root0Node71Step3Chunk3_0_checked, root0Node71Step3Chunk3_1_checked, root0Node71Step3Chunk3_2_checked, root0Node71Step3Chunk3_3_checked, root0Node71Step3Chunk3_4_checked, root0Node71Step3Chunk3_5_checked, root0Node71Step3Chunk4_0_checked, root0Node71Step3Chunk4_1_checked, root0Node71Step3Chunk4_2_checked, root0Node71Step3Chunk4_3_checked, root0Node71Step3Chunk4_4_checked, root0Node71Step3Chunk4_5_checked, root0Node71Step3Chunk5_0_checked, root0Node71Step3Chunk5_1_checked, root0Node71Step3Chunk5_2_checked, root0Node71Step3Chunk5_3_checked, root0Node71Step3Chunk5_4_checked, root0Node71Step3Chunk5_5_checked, root0Node71Step3Chunk6_0_checked, root0Node71Step3Chunk6_1_checked, root0Node71Step3Chunk6_2_checked, root0Node71Step3Chunk6_3_checked, root0Node71Step3Chunk6_4_checked, root0Node71Step3Chunk6_5_checked, root0Node71Step3Chunk7_0_checked, root0Node71Step3Chunk7_1_checked, root0Node71Step3Chunk7_2_checked, root0Node71Step3Chunk7_3_checked, root0Node71Step3Chunk7_4_checked, root0Node71Step3Chunk7_5_checked, root0Node71Step3Chunk8_0_checked, root0Node71Step3Chunk8_1_checked, root0Node71Step3Chunk8_2_checked, root0Node71Step3Chunk8_3_checked, root0Node71Step3Chunk8_4_checked, root0Node71Step3Chunk8_5_checked, Bool.true_and])
theorem root0Node71Step3_checked :
    checkReplacement table27 root0Node71Domains2 root0Node71Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root0Node71Domains2 root0Node71Domains3
    root0Node71Domains2Fast root0Node71Domains3Fast
    root0Node71Domains2_fast_eq root0Node71Domains3_fast_eq
    root0Node71Step3Narrowing_checked (by decide)
def root0Node72Domains0 : Domains 91 State := restrict root0Node71Domains3 84 (4,1)
def root0Node72Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0)]
  | 11 => some [(2,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(4,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node72Domains0_fast_eq : root0Node72Domains0 = expandDomains root0Node72Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node72Domains0 v = expandDomains root0Node72Domains0Fast v from by decide) v
def root0Node72Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(8,3)]
  | 9 => [(5,5)]
  | 10 => [(1,0)]
  | 11 => [(2,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1)]
  | 29 => [(0,1)]
  | 30 => [(7,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0)]
  | 40 => [(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2)]
  | 77 => [(7,4)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(1,1)]
  | 84 => [(4,1)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(8,0)]
  | _ => [(7,3)]
def root0Node72Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0)]
  | 11 => some [(2,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(4,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3)]
theorem root0Node72Domains1_fast_eq : root0Node72Domains1 = expandDomains root0Node72Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node72Domains1 v = expandDomains root0Node72Domains1Fast v from by decide) v
theorem root0Node72Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq (by decide)
theorem root0Node72Step1Narrowing_checked :
    checkNarrowing table56 root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root0Node72Domains0 root0Node72Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node72Step1Chunk0_0_checked, root0Node72Step1Chunk0_1_checked, root0Node72Step1Chunk0_2_checked, root0Node72Step1Chunk0_3_checked, root0Node72Step1Chunk0_4_checked, root0Node72Step1Chunk0_5_checked, root0Node72Step1Chunk1_0_checked, root0Node72Step1Chunk1_1_checked, root0Node72Step1Chunk1_2_checked, root0Node72Step1Chunk1_3_checked, root0Node72Step1Chunk1_4_checked, root0Node72Step1Chunk1_5_checked, root0Node72Step1Chunk2_0_checked, root0Node72Step1Chunk2_1_checked, root0Node72Step1Chunk2_2_checked, root0Node72Step1Chunk2_3_checked, root0Node72Step1Chunk2_4_checked, root0Node72Step1Chunk2_5_checked, root0Node72Step1Chunk3_0_checked, root0Node72Step1Chunk3_1_checked, root0Node72Step1Chunk3_2_checked, root0Node72Step1Chunk3_3_checked, root0Node72Step1Chunk3_4_checked, root0Node72Step1Chunk3_5_checked, root0Node72Step1Chunk4_0_checked, root0Node72Step1Chunk4_1_checked, root0Node72Step1Chunk4_2_checked, root0Node72Step1Chunk4_3_checked, root0Node72Step1Chunk4_4_checked, root0Node72Step1Chunk4_5_checked, root0Node72Step1Chunk5_0_checked, root0Node72Step1Chunk5_1_checked, root0Node72Step1Chunk5_2_checked, root0Node72Step1Chunk5_3_checked, root0Node72Step1Chunk5_4_checked, root0Node72Step1Chunk5_5_checked, root0Node72Step1Chunk6_0_checked, root0Node72Step1Chunk6_1_checked, root0Node72Step1Chunk6_2_checked, root0Node72Step1Chunk6_3_checked, root0Node72Step1Chunk6_4_checked, root0Node72Step1Chunk6_5_checked, root0Node72Step1Chunk7_0_checked, root0Node72Step1Chunk7_1_checked, root0Node72Step1Chunk7_2_checked, root0Node72Step1Chunk7_3_checked, root0Node72Step1Chunk7_4_checked, root0Node72Step1Chunk7_5_checked, root0Node72Step1Chunk8_0_checked, root0Node72Step1Chunk8_1_checked, root0Node72Step1Chunk8_2_checked, root0Node72Step1Chunk8_3_checked, root0Node72Step1Chunk8_4_checked, root0Node72Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node72Step1_checked :
    checkReplacement table56 root0Node72Domains0 root0Node72Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node72Domains0 root0Node72Domains1
    root0Node72Domains0Fast root0Node72Domains1Fast
    root0Node72Domains0_fast_eq root0Node72Domains1_fast_eq
    root0Node72Step1Narrowing_checked (by decide)
theorem root0Node72Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node72Domains1 (.output 35) = true := by decide
def root0Node73Domains0 : Domains 91 State := restrict root0Node71Domains3 84 (8,1)
def root0Node73Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0)]
  | 11 => some [(2,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(8,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(7,3),(8,3)]
theorem root0Node73Domains0_fast_eq : root0Node73Domains0 = expandDomains root0Node73Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node73Domains0 v = expandDomains root0Node73Domains0Fast v from by decide) v
def root0Node73Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(8,3)]
  | 9 => [(5,5)]
  | 10 => [(1,0)]
  | 11 => [(2,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(0,0)]
  | 19 => [(3,2)]
  | 20 => [(4,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(5,1)]
  | 29 => [(0,1)]
  | 30 => [(7,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(8,3)]
  | 38 => [(8,5)]
  | 39 => [(1,0)]
  | 40 => [(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(5,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(7,0)]
  | 69 => [(4,3)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2)]
  | 77 => [(7,4)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(1,1)]
  | 84 => [(8,1)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(8,0)]
  | _ => [(8,3)]
def root0Node73Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(8,3)]
  | 9 => some [(5,5)]
  | 10 => some [(1,0)]
  | 11 => some [(2,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(0,0)]
  | 19 => some [(3,2)]
  | 20 => some [(4,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(5,1)]
  | 29 => some [(0,1)]
  | 30 => some [(7,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(8,3)]
  | 38 => some [(8,5)]
  | 39 => some [(1,0)]
  | 40 => some [(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(5,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(7,0)]
  | 69 => some [(4,3)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(7,4)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(8,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(8,3)]
theorem root0Node73Domains1_fast_eq : root0Node73Domains1 = expandDomains root0Node73Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node73Domains1 v = expandDomains root0Node73Domains1Fast v from by decide) v
theorem root0Node73Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq (by decide)
theorem root0Node73Step1Narrowing_checked :
    checkNarrowing table56 root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root0Node73Domains0 root0Node73Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node73Step1Chunk0_0_checked, root0Node73Step1Chunk0_1_checked, root0Node73Step1Chunk0_2_checked, root0Node73Step1Chunk0_3_checked, root0Node73Step1Chunk0_4_checked, root0Node73Step1Chunk0_5_checked, root0Node73Step1Chunk1_0_checked, root0Node73Step1Chunk1_1_checked, root0Node73Step1Chunk1_2_checked, root0Node73Step1Chunk1_3_checked, root0Node73Step1Chunk1_4_checked, root0Node73Step1Chunk1_5_checked, root0Node73Step1Chunk2_0_checked, root0Node73Step1Chunk2_1_checked, root0Node73Step1Chunk2_2_checked, root0Node73Step1Chunk2_3_checked, root0Node73Step1Chunk2_4_checked, root0Node73Step1Chunk2_5_checked, root0Node73Step1Chunk3_0_checked, root0Node73Step1Chunk3_1_checked, root0Node73Step1Chunk3_2_checked, root0Node73Step1Chunk3_3_checked, root0Node73Step1Chunk3_4_checked, root0Node73Step1Chunk3_5_checked, root0Node73Step1Chunk4_0_checked, root0Node73Step1Chunk4_1_checked, root0Node73Step1Chunk4_2_checked, root0Node73Step1Chunk4_3_checked, root0Node73Step1Chunk4_4_checked, root0Node73Step1Chunk4_5_checked, root0Node73Step1Chunk5_0_checked, root0Node73Step1Chunk5_1_checked, root0Node73Step1Chunk5_2_checked, root0Node73Step1Chunk5_3_checked, root0Node73Step1Chunk5_4_checked, root0Node73Step1Chunk5_5_checked, root0Node73Step1Chunk6_0_checked, root0Node73Step1Chunk6_1_checked, root0Node73Step1Chunk6_2_checked, root0Node73Step1Chunk6_3_checked, root0Node73Step1Chunk6_4_checked, root0Node73Step1Chunk6_5_checked, root0Node73Step1Chunk7_0_checked, root0Node73Step1Chunk7_1_checked, root0Node73Step1Chunk7_2_checked, root0Node73Step1Chunk7_3_checked, root0Node73Step1Chunk7_4_checked, root0Node73Step1Chunk7_5_checked, root0Node73Step1Chunk8_0_checked, root0Node73Step1Chunk8_1_checked, root0Node73Step1Chunk8_2_checked, root0Node73Step1Chunk8_3_checked, root0Node73Step1Chunk8_4_checked, root0Node73Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node73Step1_checked :
    checkReplacement table56 root0Node73Domains0 root0Node73Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node73Domains0 root0Node73Domains1
    root0Node73Domains0Fast root0Node73Domains1Fast
    root0Node73Domains0_fast_eq root0Node73Domains1_fast_eq
    root0Node73Step1Narrowing_checked (by decide)
theorem root0Node73Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node73Domains1 (.output 36) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
