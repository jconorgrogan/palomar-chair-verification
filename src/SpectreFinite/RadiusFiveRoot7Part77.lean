module

public import SpectreFinite.RadiusFiveRoot7Part76
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable30
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node195Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0),(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5),(8,5)]
  | 61 => [(1,1),(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4),(3,4)]
  | 69 => [(0,5),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0),(7,0)]
  | 76 => [(2,3),(2,5)]
  | 77 => [(0,2),(6,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node195Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5),(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node195Domains2_fast_eq : root7Node195Domains2 = expandDomains root7Node195Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node195Domains2 v = expandDomains root7Node195Domains2Fast v from by decide) v
theorem root7Node195Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq (by decide)
theorem root7Node195Step2Narrowing_checked :
    checkNarrowing table30 root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkNarrowing_flatten table30Scope [table30Rows0_0,table30Rows0_1,table30Rows0_2,table30Rows0_3,table30Rows0_4,table30Rows0_5,table30Rows1_0,table30Rows1_1,table30Rows1_2,table30Rows1_3,table30Rows1_4,table30Rows1_5,table30Rows2_0,table30Rows2_1,table30Rows2_2,table30Rows2_3,table30Rows2_4,table30Rows2_5,table30Rows3_0,table30Rows3_1,table30Rows3_2,table30Rows3_3,table30Rows3_4,table30Rows3_5,table30Rows4_0,table30Rows4_1,table30Rows4_2,table30Rows4_3,table30Rows4_4,table30Rows4_5,table30Rows5_0,table30Rows5_1,table30Rows5_2,table30Rows5_3,table30Rows5_4,table30Rows5_5,table30Rows6_0,table30Rows6_1,table30Rows6_2,table30Rows6_3,table30Rows6_4,table30Rows6_5,table30Rows7_0,table30Rows7_1,table30Rows7_2,table30Rows7_3,table30Rows7_4,table30Rows7_5,table30Rows8_0,table30Rows8_1,table30Rows8_2,table30Rows8_3,table30Rows8_4,table30Rows8_5]
    root7Node195Domains1 root7Node195Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node195Step2Chunk0_0_checked, root7Node195Step2Chunk0_1_checked, root7Node195Step2Chunk0_2_checked, root7Node195Step2Chunk0_3_checked, root7Node195Step2Chunk0_4_checked, root7Node195Step2Chunk0_5_checked, root7Node195Step2Chunk1_0_checked, root7Node195Step2Chunk1_1_checked, root7Node195Step2Chunk1_2_checked, root7Node195Step2Chunk1_3_checked, root7Node195Step2Chunk1_4_checked, root7Node195Step2Chunk1_5_checked, root7Node195Step2Chunk2_0_checked, root7Node195Step2Chunk2_1_checked, root7Node195Step2Chunk2_2_checked, root7Node195Step2Chunk2_3_checked, root7Node195Step2Chunk2_4_checked, root7Node195Step2Chunk2_5_checked, root7Node195Step2Chunk3_0_checked, root7Node195Step2Chunk3_1_checked, root7Node195Step2Chunk3_2_checked, root7Node195Step2Chunk3_3_checked, root7Node195Step2Chunk3_4_checked, root7Node195Step2Chunk3_5_checked, root7Node195Step2Chunk4_0_checked, root7Node195Step2Chunk4_1_checked, root7Node195Step2Chunk4_2_checked, root7Node195Step2Chunk4_3_checked, root7Node195Step2Chunk4_4_checked, root7Node195Step2Chunk4_5_checked, root7Node195Step2Chunk5_0_checked, root7Node195Step2Chunk5_1_checked, root7Node195Step2Chunk5_2_checked, root7Node195Step2Chunk5_3_checked, root7Node195Step2Chunk5_4_checked, root7Node195Step2Chunk5_5_checked, root7Node195Step2Chunk6_0_checked, root7Node195Step2Chunk6_1_checked, root7Node195Step2Chunk6_2_checked, root7Node195Step2Chunk6_3_checked, root7Node195Step2Chunk6_4_checked, root7Node195Step2Chunk6_5_checked, root7Node195Step2Chunk7_0_checked, root7Node195Step2Chunk7_1_checked, root7Node195Step2Chunk7_2_checked, root7Node195Step2Chunk7_3_checked, root7Node195Step2Chunk7_4_checked, root7Node195Step2Chunk7_5_checked, root7Node195Step2Chunk8_0_checked, root7Node195Step2Chunk8_1_checked, root7Node195Step2Chunk8_2_checked, root7Node195Step2Chunk8_3_checked, root7Node195Step2Chunk8_4_checked, root7Node195Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node195Step2_checked :
    checkReplacement table30 root7Node195Domains1 root7Node195Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node195Domains1 root7Node195Domains2
    root7Node195Domains1Fast root7Node195Domains2Fast
    root7Node195Domains1_fast_eq root7Node195Domains2_fast_eq
    root7Node195Step2Narrowing_checked (by decide)
def root7Node196Domains0 : Domains 91 State := restrict root7Node195Domains2 30 (7,1)
def root7Node196Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0),(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5),(8,5)]
  | 61 => some [(1,1),(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node196Domains0_fast_eq : root7Node196Domains0 = expandDomains root7Node196Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node196Domains0 v = expandDomains root7Node196Domains0Fast v from by decide) v
def root7Node196Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4),(3,4)]
  | 69 => [(0,5),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0),(7,0)]
  | 76 => [(2,3),(2,5)]
  | 77 => [(0,2),(6,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node196Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node196Domains1_fast_eq : root7Node196Domains1 = expandDomains root7Node196Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node196Domains1 v = expandDomains root7Node196Domains1Fast v from by decide) v
theorem root7Node196Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq (by decide)
theorem root7Node196Step1Narrowing_checked :
    checkNarrowing table21 root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root7Node196Domains0 root7Node196Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node196Step1Chunk0_0_checked, root7Node196Step1Chunk0_1_checked, root7Node196Step1Chunk0_2_checked, root7Node196Step1Chunk0_3_checked, root7Node196Step1Chunk0_4_checked, root7Node196Step1Chunk0_5_checked, root7Node196Step1Chunk1_0_checked, root7Node196Step1Chunk1_1_checked, root7Node196Step1Chunk1_2_checked, root7Node196Step1Chunk1_3_checked, root7Node196Step1Chunk1_4_checked, root7Node196Step1Chunk1_5_checked, root7Node196Step1Chunk2_0_checked, root7Node196Step1Chunk2_1_checked, root7Node196Step1Chunk2_2_checked, root7Node196Step1Chunk2_3_checked, root7Node196Step1Chunk2_4_checked, root7Node196Step1Chunk2_5_checked, root7Node196Step1Chunk3_0_checked, root7Node196Step1Chunk3_1_checked, root7Node196Step1Chunk3_2_checked, root7Node196Step1Chunk3_3_checked, root7Node196Step1Chunk3_4_checked, root7Node196Step1Chunk3_5_checked, root7Node196Step1Chunk4_0_checked, root7Node196Step1Chunk4_1_checked, root7Node196Step1Chunk4_2_checked, root7Node196Step1Chunk4_3_checked, root7Node196Step1Chunk4_4_checked, root7Node196Step1Chunk4_5_checked, root7Node196Step1Chunk5_0_checked, root7Node196Step1Chunk5_1_checked, root7Node196Step1Chunk5_2_checked, root7Node196Step1Chunk5_3_checked, root7Node196Step1Chunk5_4_checked, root7Node196Step1Chunk5_5_checked, root7Node196Step1Chunk6_0_checked, root7Node196Step1Chunk6_1_checked, root7Node196Step1Chunk6_2_checked, root7Node196Step1Chunk6_3_checked, root7Node196Step1Chunk6_4_checked, root7Node196Step1Chunk6_5_checked, root7Node196Step1Chunk7_0_checked, root7Node196Step1Chunk7_1_checked, root7Node196Step1Chunk7_2_checked, root7Node196Step1Chunk7_3_checked, root7Node196Step1Chunk7_4_checked, root7Node196Step1Chunk7_5_checked, root7Node196Step1Chunk8_0_checked, root7Node196Step1Chunk8_1_checked, root7Node196Step1Chunk8_2_checked, root7Node196Step1Chunk8_3_checked, root7Node196Step1Chunk8_4_checked, root7Node196Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node196Step1_checked :
    checkReplacement table21 root7Node196Domains0 root7Node196Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node196Domains0 root7Node196Domains1
    root7Node196Domains0Fast root7Node196Domains1Fast
    root7Node196Domains0_fast_eq root7Node196Domains1_fast_eq
    root7Node196Step1Narrowing_checked (by decide)
def root7Node197Domains0 : Domains 91 State := restrict root7Node196Domains1 60 (5,5)
def root7Node197Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node197Domains0_fast_eq : root7Node197Domains0 = expandDomains root7Node197Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node197Domains0 v = expandDomains root7Node197Domains0Fast v from by decide) v
def root7Node197Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4)]
  | 69 => [(0,5)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0)]
  | 76 => [(2,5)]
  | 77 => [(6,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node197Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4)]
  | 69 => some [(0,5)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0)]
  | 76 => some [(2,5)]
  | 77 => some [(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node197Domains1_fast_eq : root7Node197Domains1 = expandDomains root7Node197Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node197Domains1 v = expandDomains root7Node197Domains1Fast v from by decide) v
theorem root7Node197Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq (by decide)
theorem root7Node197Step1Narrowing_checked :
    checkNarrowing table56 root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node197Domains0 root7Node197Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node197Step1Chunk0_0_checked, root7Node197Step1Chunk0_1_checked, root7Node197Step1Chunk0_2_checked, root7Node197Step1Chunk0_3_checked, root7Node197Step1Chunk0_4_checked, root7Node197Step1Chunk0_5_checked, root7Node197Step1Chunk1_0_checked, root7Node197Step1Chunk1_1_checked, root7Node197Step1Chunk1_2_checked, root7Node197Step1Chunk1_3_checked, root7Node197Step1Chunk1_4_checked, root7Node197Step1Chunk1_5_checked, root7Node197Step1Chunk2_0_checked, root7Node197Step1Chunk2_1_checked, root7Node197Step1Chunk2_2_checked, root7Node197Step1Chunk2_3_checked, root7Node197Step1Chunk2_4_checked, root7Node197Step1Chunk2_5_checked, root7Node197Step1Chunk3_0_checked, root7Node197Step1Chunk3_1_checked, root7Node197Step1Chunk3_2_checked, root7Node197Step1Chunk3_3_checked, root7Node197Step1Chunk3_4_checked, root7Node197Step1Chunk3_5_checked, root7Node197Step1Chunk4_0_checked, root7Node197Step1Chunk4_1_checked, root7Node197Step1Chunk4_2_checked, root7Node197Step1Chunk4_3_checked, root7Node197Step1Chunk4_4_checked, root7Node197Step1Chunk4_5_checked, root7Node197Step1Chunk5_0_checked, root7Node197Step1Chunk5_1_checked, root7Node197Step1Chunk5_2_checked, root7Node197Step1Chunk5_3_checked, root7Node197Step1Chunk5_4_checked, root7Node197Step1Chunk5_5_checked, root7Node197Step1Chunk6_0_checked, root7Node197Step1Chunk6_1_checked, root7Node197Step1Chunk6_2_checked, root7Node197Step1Chunk6_3_checked, root7Node197Step1Chunk6_4_checked, root7Node197Step1Chunk6_5_checked, root7Node197Step1Chunk7_0_checked, root7Node197Step1Chunk7_1_checked, root7Node197Step1Chunk7_2_checked, root7Node197Step1Chunk7_3_checked, root7Node197Step1Chunk7_4_checked, root7Node197Step1Chunk7_5_checked, root7Node197Step1Chunk8_0_checked, root7Node197Step1Chunk8_1_checked, root7Node197Step1Chunk8_2_checked, root7Node197Step1Chunk8_3_checked, root7Node197Step1Chunk8_4_checked, root7Node197Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node197Step1_checked :
    checkReplacement table56 root7Node197Domains0 root7Node197Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node197Domains0 root7Node197Domains1
    root7Node197Domains0Fast root7Node197Domains1Fast
    root7Node197Domains0_fast_eq root7Node197Domains1_fast_eq
    root7Node197Step1Narrowing_checked (by decide)
theorem root7Node197Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node197Domains1 (.output 97) = true := by decide
def root7Node198Domains0 : Domains 91 State := restrict root7Node196Domains1 60 (8,5)
def root7Node198Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node198Domains0_fast_eq : root7Node198Domains0 = expandDomains root7Node198Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node198Domains0 v = expandDomains root7Node198Domains0Fast v from by decide) v
def root7Node198Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(3,4)]
  | 69 => [(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(2,3)]
  | 77 => [(0,2)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root7Node198Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(3,4)]
  | 69 => some [(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(2,3)]
  | 77 => some [(0,2)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root7Node198Domains1_fast_eq : root7Node198Domains1 = expandDomains root7Node198Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node198Domains1 v = expandDomains root7Node198Domains1Fast v from by decide) v
theorem root7Node198Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq (by decide)
theorem root7Node198Step1Narrowing_checked :
    checkNarrowing table56 root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node198Domains0 root7Node198Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node198Step1Chunk0_0_checked, root7Node198Step1Chunk0_1_checked, root7Node198Step1Chunk0_2_checked, root7Node198Step1Chunk0_3_checked, root7Node198Step1Chunk0_4_checked, root7Node198Step1Chunk0_5_checked, root7Node198Step1Chunk1_0_checked, root7Node198Step1Chunk1_1_checked, root7Node198Step1Chunk1_2_checked, root7Node198Step1Chunk1_3_checked, root7Node198Step1Chunk1_4_checked, root7Node198Step1Chunk1_5_checked, root7Node198Step1Chunk2_0_checked, root7Node198Step1Chunk2_1_checked, root7Node198Step1Chunk2_2_checked, root7Node198Step1Chunk2_3_checked, root7Node198Step1Chunk2_4_checked, root7Node198Step1Chunk2_5_checked, root7Node198Step1Chunk3_0_checked, root7Node198Step1Chunk3_1_checked, root7Node198Step1Chunk3_2_checked, root7Node198Step1Chunk3_3_checked, root7Node198Step1Chunk3_4_checked, root7Node198Step1Chunk3_5_checked, root7Node198Step1Chunk4_0_checked, root7Node198Step1Chunk4_1_checked, root7Node198Step1Chunk4_2_checked, root7Node198Step1Chunk4_3_checked, root7Node198Step1Chunk4_4_checked, root7Node198Step1Chunk4_5_checked, root7Node198Step1Chunk5_0_checked, root7Node198Step1Chunk5_1_checked, root7Node198Step1Chunk5_2_checked, root7Node198Step1Chunk5_3_checked, root7Node198Step1Chunk5_4_checked, root7Node198Step1Chunk5_5_checked, root7Node198Step1Chunk6_0_checked, root7Node198Step1Chunk6_1_checked, root7Node198Step1Chunk6_2_checked, root7Node198Step1Chunk6_3_checked, root7Node198Step1Chunk6_4_checked, root7Node198Step1Chunk6_5_checked, root7Node198Step1Chunk7_0_checked, root7Node198Step1Chunk7_1_checked, root7Node198Step1Chunk7_2_checked, root7Node198Step1Chunk7_3_checked, root7Node198Step1Chunk7_4_checked, root7Node198Step1Chunk7_5_checked, root7Node198Step1Chunk8_0_checked, root7Node198Step1Chunk8_1_checked, root7Node198Step1Chunk8_2_checked, root7Node198Step1Chunk8_3_checked, root7Node198Step1Chunk8_4_checked, root7Node198Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node198Step1_checked :
    checkReplacement table56 root7Node198Domains0 root7Node198Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node198Domains0 root7Node198Domains1
    root7Node198Domains0Fast root7Node198Domains1Fast
    root7Node198Domains0_fast_eq root7Node198Domains1_fast_eq
    root7Node198Step1Narrowing_checked (by decide)
theorem root7Node198Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node198Domains1 (.output 98) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
