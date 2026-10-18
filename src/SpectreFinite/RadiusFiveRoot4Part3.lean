module

public import SpectreFinite.RadiusFiveRoot4Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable4
public import SpectreFinite.RadiusFiveTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node4Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0),(2,4)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(3,0)]
  | 33 => [(2,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1),(7,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node4Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node4Domains2_fast_eq : root4Node4Domains2 = expandDomains root4Node4Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node4Domains2 v = expandDomains root4Node4Domains2Fast v from by decide) v
theorem root4Node4Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq (by decide)
theorem root4Node4Step2Narrowing_checked :
    checkNarrowing table4 root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkNarrowing_flatten table4Scope [table4Rows0_0,table4Rows0_1,table4Rows0_2,table4Rows0_3,table4Rows0_4,table4Rows0_5,table4Rows1_0,table4Rows1_1,table4Rows1_2,table4Rows1_3,table4Rows1_4,table4Rows1_5,table4Rows2_0,table4Rows2_1,table4Rows2_2,table4Rows2_3,table4Rows2_4,table4Rows2_5,table4Rows3_0,table4Rows3_1,table4Rows3_2,table4Rows3_3,table4Rows3_4,table4Rows3_5,table4Rows4_0,table4Rows4_1,table4Rows4_2,table4Rows4_3,table4Rows4_4,table4Rows4_5,table4Rows5_0,table4Rows5_1,table4Rows5_2,table4Rows5_3,table4Rows5_4,table4Rows5_5,table4Rows6_0,table4Rows6_1,table4Rows6_2,table4Rows6_3,table4Rows6_4,table4Rows6_5,table4Rows7_0,table4Rows7_1,table4Rows7_2,table4Rows7_3,table4Rows7_4,table4Rows7_5,table4Rows8_0,table4Rows8_1,table4Rows8_2,table4Rows8_3,table4Rows8_4,table4Rows8_5]
    root4Node4Domains1 root4Node4Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node4Step2Chunk0_0_checked, root4Node4Step2Chunk0_1_checked, root4Node4Step2Chunk0_2_checked, root4Node4Step2Chunk0_3_checked, root4Node4Step2Chunk0_4_checked, root4Node4Step2Chunk0_5_checked, root4Node4Step2Chunk1_0_checked, root4Node4Step2Chunk1_1_checked, root4Node4Step2Chunk1_2_checked, root4Node4Step2Chunk1_3_checked, root4Node4Step2Chunk1_4_checked, root4Node4Step2Chunk1_5_checked, root4Node4Step2Chunk2_0_checked, root4Node4Step2Chunk2_1_checked, root4Node4Step2Chunk2_2_checked, root4Node4Step2Chunk2_3_checked, root4Node4Step2Chunk2_4_checked, root4Node4Step2Chunk2_5_checked, root4Node4Step2Chunk3_0_checked, root4Node4Step2Chunk3_1_checked, root4Node4Step2Chunk3_2_checked, root4Node4Step2Chunk3_3_checked, root4Node4Step2Chunk3_4_checked, root4Node4Step2Chunk3_5_checked, root4Node4Step2Chunk4_0_checked, root4Node4Step2Chunk4_1_checked, root4Node4Step2Chunk4_2_checked, root4Node4Step2Chunk4_3_checked, root4Node4Step2Chunk4_4_checked, root4Node4Step2Chunk4_5_checked, root4Node4Step2Chunk5_0_checked, root4Node4Step2Chunk5_1_checked, root4Node4Step2Chunk5_2_checked, root4Node4Step2Chunk5_3_checked, root4Node4Step2Chunk5_4_checked, root4Node4Step2Chunk5_5_checked, root4Node4Step2Chunk6_0_checked, root4Node4Step2Chunk6_1_checked, root4Node4Step2Chunk6_2_checked, root4Node4Step2Chunk6_3_checked, root4Node4Step2Chunk6_4_checked, root4Node4Step2Chunk6_5_checked, root4Node4Step2Chunk7_0_checked, root4Node4Step2Chunk7_1_checked, root4Node4Step2Chunk7_2_checked, root4Node4Step2Chunk7_3_checked, root4Node4Step2Chunk7_4_checked, root4Node4Step2Chunk7_5_checked, root4Node4Step2Chunk8_0_checked, root4Node4Step2Chunk8_1_checked, root4Node4Step2Chunk8_2_checked, root4Node4Step2Chunk8_3_checked, root4Node4Step2Chunk8_4_checked, root4Node4Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node4Step2_checked :
    checkReplacement table4 root4Node4Domains1 root4Node4Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node4Domains1 root4Node4Domains2
    root4Node4Domains1Fast root4Node4Domains2Fast
    root4Node4Domains1_fast_eq root4Node4Domains2_fast_eq
    root4Node4Step2Narrowing_checked (by decide)
def root4Node5Domains0 : Domains 91 State := restrict root4Node4Domains2 20 (1,5)
def root4Node5Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node5Domains0_fast_eq : root4Node5Domains0 = expandDomains root4Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node5Domains0 v = expandDomains root4Node5Domains0Fast v from by decide) v
def root4Node5Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(3,0)]
  | 33 => [(2,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node5Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node5Domains1_fast_eq : root4Node5Domains1 = expandDomains root4Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node5Domains1 v = expandDomains root4Node5Domains1Fast v from by decide) v
theorem root4Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq (by decide)
theorem root4Node5Step1Narrowing_checked :
    checkNarrowing table12 root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root4Node5Domains0 root4Node5Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node5Step1Chunk0_0_checked, root4Node5Step1Chunk0_1_checked, root4Node5Step1Chunk0_2_checked, root4Node5Step1Chunk0_3_checked, root4Node5Step1Chunk0_4_checked, root4Node5Step1Chunk0_5_checked, root4Node5Step1Chunk1_0_checked, root4Node5Step1Chunk1_1_checked, root4Node5Step1Chunk1_2_checked, root4Node5Step1Chunk1_3_checked, root4Node5Step1Chunk1_4_checked, root4Node5Step1Chunk1_5_checked, root4Node5Step1Chunk2_0_checked, root4Node5Step1Chunk2_1_checked, root4Node5Step1Chunk2_2_checked, root4Node5Step1Chunk2_3_checked, root4Node5Step1Chunk2_4_checked, root4Node5Step1Chunk2_5_checked, root4Node5Step1Chunk3_0_checked, root4Node5Step1Chunk3_1_checked, root4Node5Step1Chunk3_2_checked, root4Node5Step1Chunk3_3_checked, root4Node5Step1Chunk3_4_checked, root4Node5Step1Chunk3_5_checked, root4Node5Step1Chunk4_0_checked, root4Node5Step1Chunk4_1_checked, root4Node5Step1Chunk4_2_checked, root4Node5Step1Chunk4_3_checked, root4Node5Step1Chunk4_4_checked, root4Node5Step1Chunk4_5_checked, root4Node5Step1Chunk5_0_checked, root4Node5Step1Chunk5_1_checked, root4Node5Step1Chunk5_2_checked, root4Node5Step1Chunk5_3_checked, root4Node5Step1Chunk5_4_checked, root4Node5Step1Chunk5_5_checked, root4Node5Step1Chunk6_0_checked, root4Node5Step1Chunk6_1_checked, root4Node5Step1Chunk6_2_checked, root4Node5Step1Chunk6_3_checked, root4Node5Step1Chunk6_4_checked, root4Node5Step1Chunk6_5_checked, root4Node5Step1Chunk7_0_checked, root4Node5Step1Chunk7_1_checked, root4Node5Step1Chunk7_2_checked, root4Node5Step1Chunk7_3_checked, root4Node5Step1Chunk7_4_checked, root4Node5Step1Chunk7_5_checked, root4Node5Step1Chunk8_0_checked, root4Node5Step1Chunk8_1_checked, root4Node5Step1Chunk8_2_checked, root4Node5Step1Chunk8_3_checked, root4Node5Step1Chunk8_4_checked, root4Node5Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node5Step1_checked :
    checkReplacement table12 root4Node5Domains0 root4Node5Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node5Domains0 root4Node5Domains1
    root4Node5Domains0Fast root4Node5Domains1Fast
    root4Node5Domains0_fast_eq root4Node5Domains1_fast_eq
    root4Node5Step1Narrowing_checked (by decide)
theorem root4Node5Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node5Domains1 (.output 0) = true := by decide
def root4Node6Domains0 : Domains 91 State := restrict root4Node4Domains2 20 (3,5)
def root4Node6Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node6Domains0_fast_eq : root4Node6Domains0 = expandDomains root4Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node6Domains0 v = expandDomains root4Node6Domains0Fast v from by decide) v
def root4Node6Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(3,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,4)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(3,0)]
  | 33 => [(2,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(6,5)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(7,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node6Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(6,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(7,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node6Domains1_fast_eq : root4Node6Domains1 = expandDomains root4Node6Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node6Domains1 v = expandDomains root4Node6Domains1Fast v from by decide) v
theorem root4Node6Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq (by decide)
theorem root4Node6Step1Narrowing_checked :
    checkNarrowing table12 root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root4Node6Domains0 root4Node6Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node6Step1Chunk0_0_checked, root4Node6Step1Chunk0_1_checked, root4Node6Step1Chunk0_2_checked, root4Node6Step1Chunk0_3_checked, root4Node6Step1Chunk0_4_checked, root4Node6Step1Chunk0_5_checked, root4Node6Step1Chunk1_0_checked, root4Node6Step1Chunk1_1_checked, root4Node6Step1Chunk1_2_checked, root4Node6Step1Chunk1_3_checked, root4Node6Step1Chunk1_4_checked, root4Node6Step1Chunk1_5_checked, root4Node6Step1Chunk2_0_checked, root4Node6Step1Chunk2_1_checked, root4Node6Step1Chunk2_2_checked, root4Node6Step1Chunk2_3_checked, root4Node6Step1Chunk2_4_checked, root4Node6Step1Chunk2_5_checked, root4Node6Step1Chunk3_0_checked, root4Node6Step1Chunk3_1_checked, root4Node6Step1Chunk3_2_checked, root4Node6Step1Chunk3_3_checked, root4Node6Step1Chunk3_4_checked, root4Node6Step1Chunk3_5_checked, root4Node6Step1Chunk4_0_checked, root4Node6Step1Chunk4_1_checked, root4Node6Step1Chunk4_2_checked, root4Node6Step1Chunk4_3_checked, root4Node6Step1Chunk4_4_checked, root4Node6Step1Chunk4_5_checked, root4Node6Step1Chunk5_0_checked, root4Node6Step1Chunk5_1_checked, root4Node6Step1Chunk5_2_checked, root4Node6Step1Chunk5_3_checked, root4Node6Step1Chunk5_4_checked, root4Node6Step1Chunk5_5_checked, root4Node6Step1Chunk6_0_checked, root4Node6Step1Chunk6_1_checked, root4Node6Step1Chunk6_2_checked, root4Node6Step1Chunk6_3_checked, root4Node6Step1Chunk6_4_checked, root4Node6Step1Chunk6_5_checked, root4Node6Step1Chunk7_0_checked, root4Node6Step1Chunk7_1_checked, root4Node6Step1Chunk7_2_checked, root4Node6Step1Chunk7_3_checked, root4Node6Step1Chunk7_4_checked, root4Node6Step1Chunk7_5_checked, root4Node6Step1Chunk8_0_checked, root4Node6Step1Chunk8_1_checked, root4Node6Step1Chunk8_2_checked, root4Node6Step1Chunk8_3_checked, root4Node6Step1Chunk8_4_checked, root4Node6Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node6Step1_checked :
    checkReplacement table12 root4Node6Domains0 root4Node6Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node6Domains0 root4Node6Domains1
    root4Node6Domains0Fast root4Node6Domains1Fast
    root4Node6Domains0_fast_eq root4Node6Domains1_fast_eq
    root4Node6Step1Narrowing_checked (by decide)
theorem root4Node6Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node6Domains1 (.output 1) = true := by decide
def root4Node7Domains0 : Domains 91 State := restrict root4Node3Domains2 17 (8,5)
def root4Node7Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4),(3,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(4,4),(7,2)]
  | 27 => some [(1,4),(7,4)]
  | 28 => some [(0,5),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0),(7,0)]
  | 33 => some [(2,3),(2,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0),(6,4)]
  | 44 => some [(1,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2),(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0),(8,0)]
  | 62 => some [(4,5),(7,3)]
  | 63 => some [(4,2),(7,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,3),(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(5,3),(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node7Domains0_fast_eq : root4Node7Domains0 = expandDomains root4Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node7Domains0 v = expandDomains root4Node7Domains0Fast v from by decide) v
def root4Node7Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(3,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(2,3)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(6,4)]
  | 44 => [(1,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0),(8,0)]
  | 62 => [(4,5),(7,3)]
  | 63 => [(4,2)]
  | 64 => [(5,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0),(6,4)]
  | 71 => [(1,2),(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,3),(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(5,3),(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root4Node7Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0),(8,0)]
  | 62 => some [(4,5),(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,3),(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(5,3),(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node7Domains1_fast_eq : root4Node7Domains1 = expandDomains root4Node7Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node7Domains1 v = expandDomains root4Node7Domains1Fast v from by decide) v
theorem root4Node7Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq (by decide)
theorem root4Node7Step1Narrowing_checked :
    checkNarrowing table46 root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root4Node7Domains0 root4Node7Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node7Step1Chunk0_0_checked, root4Node7Step1Chunk0_1_checked, root4Node7Step1Chunk0_2_checked, root4Node7Step1Chunk0_3_checked, root4Node7Step1Chunk0_4_checked, root4Node7Step1Chunk0_5_checked, root4Node7Step1Chunk1_0_checked, root4Node7Step1Chunk1_1_checked, root4Node7Step1Chunk1_2_checked, root4Node7Step1Chunk1_3_checked, root4Node7Step1Chunk1_4_checked, root4Node7Step1Chunk1_5_checked, root4Node7Step1Chunk2_0_checked, root4Node7Step1Chunk2_1_checked, root4Node7Step1Chunk2_2_checked, root4Node7Step1Chunk2_3_checked, root4Node7Step1Chunk2_4_checked, root4Node7Step1Chunk2_5_checked, root4Node7Step1Chunk3_0_checked, root4Node7Step1Chunk3_1_checked, root4Node7Step1Chunk3_2_checked, root4Node7Step1Chunk3_3_checked, root4Node7Step1Chunk3_4_checked, root4Node7Step1Chunk3_5_checked, root4Node7Step1Chunk4_0_checked, root4Node7Step1Chunk4_1_checked, root4Node7Step1Chunk4_2_checked, root4Node7Step1Chunk4_3_checked, root4Node7Step1Chunk4_4_checked, root4Node7Step1Chunk4_5_checked, root4Node7Step1Chunk5_0_checked, root4Node7Step1Chunk5_1_checked, root4Node7Step1Chunk5_2_checked, root4Node7Step1Chunk5_3_checked, root4Node7Step1Chunk5_4_checked, root4Node7Step1Chunk5_5_checked, root4Node7Step1Chunk6_0_checked, root4Node7Step1Chunk6_1_checked, root4Node7Step1Chunk6_2_checked, root4Node7Step1Chunk6_3_checked, root4Node7Step1Chunk6_4_checked, root4Node7Step1Chunk6_5_checked, root4Node7Step1Chunk7_0_checked, root4Node7Step1Chunk7_1_checked, root4Node7Step1Chunk7_2_checked, root4Node7Step1Chunk7_3_checked, root4Node7Step1Chunk7_4_checked, root4Node7Step1Chunk7_5_checked, root4Node7Step1Chunk8_0_checked, root4Node7Step1Chunk8_1_checked, root4Node7Step1Chunk8_2_checked, root4Node7Step1Chunk8_3_checked, root4Node7Step1Chunk8_4_checked, root4Node7Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node7Step1_checked :
    checkReplacement table46 root4Node7Domains0 root4Node7Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node7Domains0 root4Node7Domains1
    root4Node7Domains0Fast root4Node7Domains1Fast
    root4Node7Domains0_fast_eq root4Node7Domains1_fast_eq
    root4Node7Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
