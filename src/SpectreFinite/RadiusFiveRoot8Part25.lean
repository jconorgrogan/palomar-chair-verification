module

public import SpectreFinite.RadiusFiveRoot8Part24
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node61Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(2,5),(4,5)]
  | 7 => [(1,0),(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4),(8,4)]
  | 30 => [(2,5),(4,5),(7,3),(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node61Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(2,5),(4,5),(7,3),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node61Domains2_fast_eq : root8Node61Domains2 = expandDomains root8Node61Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node61Domains2 v = expandDomains root8Node61Domains2Fast v from by decide) v
theorem root8Node61Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq (by decide)
theorem root8Node61Step2Narrowing_checked :
    checkNarrowing table65 root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root8Node61Domains1 root8Node61Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node61Step2Chunk0_0_checked, root8Node61Step2Chunk0_1_checked, root8Node61Step2Chunk0_2_checked, root8Node61Step2Chunk0_3_checked, root8Node61Step2Chunk0_4_checked, root8Node61Step2Chunk0_5_checked, root8Node61Step2Chunk1_0_checked, root8Node61Step2Chunk1_1_checked, root8Node61Step2Chunk1_2_checked, root8Node61Step2Chunk1_3_checked, root8Node61Step2Chunk1_4_checked, root8Node61Step2Chunk1_5_checked, root8Node61Step2Chunk2_0_checked, root8Node61Step2Chunk2_1_checked, root8Node61Step2Chunk2_2_checked, root8Node61Step2Chunk2_3_checked, root8Node61Step2Chunk2_4_checked, root8Node61Step2Chunk2_5_checked, root8Node61Step2Chunk3_0_checked, root8Node61Step2Chunk3_1_checked, root8Node61Step2Chunk3_2_checked, root8Node61Step2Chunk3_3_checked, root8Node61Step2Chunk3_4_checked, root8Node61Step2Chunk3_5_checked, root8Node61Step2Chunk4_0_checked, root8Node61Step2Chunk4_1_checked, root8Node61Step2Chunk4_2_checked, root8Node61Step2Chunk4_3_checked, root8Node61Step2Chunk4_4_checked, root8Node61Step2Chunk4_5_checked, root8Node61Step2Chunk5_0_checked, root8Node61Step2Chunk5_1_checked, root8Node61Step2Chunk5_2_checked, root8Node61Step2Chunk5_3_checked, root8Node61Step2Chunk5_4_checked, root8Node61Step2Chunk5_5_checked, root8Node61Step2Chunk6_0_checked, root8Node61Step2Chunk6_1_checked, root8Node61Step2Chunk6_2_checked, root8Node61Step2Chunk6_3_checked, root8Node61Step2Chunk6_4_checked, root8Node61Step2Chunk6_5_checked, root8Node61Step2Chunk7_0_checked, root8Node61Step2Chunk7_1_checked, root8Node61Step2Chunk7_2_checked, root8Node61Step2Chunk7_3_checked, root8Node61Step2Chunk7_4_checked, root8Node61Step2Chunk7_5_checked, root8Node61Step2Chunk8_0_checked, root8Node61Step2Chunk8_1_checked, root8Node61Step2Chunk8_2_checked, root8Node61Step2Chunk8_3_checked, root8Node61Step2Chunk8_4_checked, root8Node61Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node61Step2_checked :
    checkReplacement table65 root8Node61Domains1 root8Node61Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node61Domains1 root8Node61Domains2
    root8Node61Domains1Fast root8Node61Domains2Fast
    root8Node61Domains1_fast_eq root8Node61Domains2_fast_eq
    root8Node61Step2Narrowing_checked (by decide)
def root8Node61Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(2,5),(4,5)]
  | 7 => [(1,0),(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4),(8,4)]
  | 30 => [(4,5),(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0),(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node61Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node61Domains3_fast_eq : root8Node61Domains3 = expandDomains root8Node61Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node61Domains3 v = expandDomains root8Node61Domains3Fast v from by decide) v
theorem root8Node61Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq (by decide)
theorem root8Node61Step3Narrowing_checked :
    checkNarrowing table13 root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root8Node61Domains2 root8Node61Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node61Step3Chunk0_0_checked, root8Node61Step3Chunk0_1_checked, root8Node61Step3Chunk0_2_checked, root8Node61Step3Chunk0_3_checked, root8Node61Step3Chunk0_4_checked, root8Node61Step3Chunk0_5_checked, root8Node61Step3Chunk1_0_checked, root8Node61Step3Chunk1_1_checked, root8Node61Step3Chunk1_2_checked, root8Node61Step3Chunk1_3_checked, root8Node61Step3Chunk1_4_checked, root8Node61Step3Chunk1_5_checked, root8Node61Step3Chunk2_0_checked, root8Node61Step3Chunk2_1_checked, root8Node61Step3Chunk2_2_checked, root8Node61Step3Chunk2_3_checked, root8Node61Step3Chunk2_4_checked, root8Node61Step3Chunk2_5_checked, root8Node61Step3Chunk3_0_checked, root8Node61Step3Chunk3_1_checked, root8Node61Step3Chunk3_2_checked, root8Node61Step3Chunk3_3_checked, root8Node61Step3Chunk3_4_checked, root8Node61Step3Chunk3_5_checked, root8Node61Step3Chunk4_0_checked, root8Node61Step3Chunk4_1_checked, root8Node61Step3Chunk4_2_checked, root8Node61Step3Chunk4_3_checked, root8Node61Step3Chunk4_4_checked, root8Node61Step3Chunk4_5_checked, root8Node61Step3Chunk5_0_checked, root8Node61Step3Chunk5_1_checked, root8Node61Step3Chunk5_2_checked, root8Node61Step3Chunk5_3_checked, root8Node61Step3Chunk5_4_checked, root8Node61Step3Chunk5_5_checked, root8Node61Step3Chunk6_0_checked, root8Node61Step3Chunk6_1_checked, root8Node61Step3Chunk6_2_checked, root8Node61Step3Chunk6_3_checked, root8Node61Step3Chunk6_4_checked, root8Node61Step3Chunk6_5_checked, root8Node61Step3Chunk7_0_checked, root8Node61Step3Chunk7_1_checked, root8Node61Step3Chunk7_2_checked, root8Node61Step3Chunk7_3_checked, root8Node61Step3Chunk7_4_checked, root8Node61Step3Chunk7_5_checked, root8Node61Step3Chunk8_0_checked, root8Node61Step3Chunk8_1_checked, root8Node61Step3Chunk8_2_checked, root8Node61Step3Chunk8_3_checked, root8Node61Step3Chunk8_4_checked, root8Node61Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node61Step3_checked :
    checkReplacement table13 root8Node61Domains2 root8Node61Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node61Domains2 root8Node61Domains3
    root8Node61Domains2Fast root8Node61Domains3Fast
    root8Node61Domains2_fast_eq root8Node61Domains3_fast_eq
    root8Node61Step3Narrowing_checked (by decide)
def root8Node61Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(2,5),(4,5)]
  | 7 => [(1,0),(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4),(8,4)]
  | 30 => [(4,5),(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5),(6,5)]
  | 40 => [(0,0),(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node61Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node61Domains4_fast_eq : root8Node61Domains4 = expandDomains root8Node61Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node61Domains4 v = expandDomains root8Node61Domains4Fast v from by decide) v
theorem root8Node61Step4Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq (by decide)
theorem root8Node61Step4Narrowing_checked :
    checkNarrowing table19 root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root8Node61Domains3 root8Node61Domains4 (by
      simp only [List.all_cons, List.all_nil, root8Node61Step4Chunk0_0_checked, root8Node61Step4Chunk0_1_checked, root8Node61Step4Chunk0_2_checked, root8Node61Step4Chunk0_3_checked, root8Node61Step4Chunk0_4_checked, root8Node61Step4Chunk0_5_checked, root8Node61Step4Chunk1_0_checked, root8Node61Step4Chunk1_1_checked, root8Node61Step4Chunk1_2_checked, root8Node61Step4Chunk1_3_checked, root8Node61Step4Chunk1_4_checked, root8Node61Step4Chunk1_5_checked, root8Node61Step4Chunk2_0_checked, root8Node61Step4Chunk2_1_checked, root8Node61Step4Chunk2_2_checked, root8Node61Step4Chunk2_3_checked, root8Node61Step4Chunk2_4_checked, root8Node61Step4Chunk2_5_checked, root8Node61Step4Chunk3_0_checked, root8Node61Step4Chunk3_1_checked, root8Node61Step4Chunk3_2_checked, root8Node61Step4Chunk3_3_checked, root8Node61Step4Chunk3_4_checked, root8Node61Step4Chunk3_5_checked, root8Node61Step4Chunk4_0_checked, root8Node61Step4Chunk4_1_checked, root8Node61Step4Chunk4_2_checked, root8Node61Step4Chunk4_3_checked, root8Node61Step4Chunk4_4_checked, root8Node61Step4Chunk4_5_checked, root8Node61Step4Chunk5_0_checked, root8Node61Step4Chunk5_1_checked, root8Node61Step4Chunk5_2_checked, root8Node61Step4Chunk5_3_checked, root8Node61Step4Chunk5_4_checked, root8Node61Step4Chunk5_5_checked, root8Node61Step4Chunk6_0_checked, root8Node61Step4Chunk6_1_checked, root8Node61Step4Chunk6_2_checked, root8Node61Step4Chunk6_3_checked, root8Node61Step4Chunk6_4_checked, root8Node61Step4Chunk6_5_checked, root8Node61Step4Chunk7_0_checked, root8Node61Step4Chunk7_1_checked, root8Node61Step4Chunk7_2_checked, root8Node61Step4Chunk7_3_checked, root8Node61Step4Chunk7_4_checked, root8Node61Step4Chunk7_5_checked, root8Node61Step4Chunk8_0_checked, root8Node61Step4Chunk8_1_checked, root8Node61Step4Chunk8_2_checked, root8Node61Step4Chunk8_3_checked, root8Node61Step4Chunk8_4_checked, root8Node61Step4Chunk8_5_checked, Bool.true_and])
theorem root8Node61Step4_checked :
    checkReplacement table19 root8Node61Domains3 root8Node61Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root8Node61Domains3 root8Node61Domains4
    root8Node61Domains3Fast root8Node61Domains4Fast
    root8Node61Domains3_fast_eq root8Node61Domains4_fast_eq
    root8Node61Step4Narrowing_checked (by decide)
def root8Node62Domains0 : Domains 91 State := restrict root8Node61Domains4 0 (0,1)
def root8Node62Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node62Domains0_fast_eq : root8Node62Domains0 = expandDomains root8Node62Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node62Domains0 v = expandDomains root8Node62Domains0Fast v from by decide) v
def root8Node62Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,4)]
  | 6 => [(4,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2),(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(7,4),(8,4)]
  | 30 => [(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5),(6,5)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node62Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,4)]
  | 6 => some [(4,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(7,4),(8,4)]
  | 30 => some [(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node62Domains1_fast_eq : root8Node62Domains1 = expandDomains root8Node62Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node62Domains1 v = expandDomains root8Node62Domains1Fast v from by decide) v
theorem root8Node62Step1Chunk0_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Narrowing_checked :
    checkNarrowing table33 root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root8Node62Domains0 root8Node62Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node62Step1Chunk0_0_checked, root8Node62Step1Chunk0_1_checked, root8Node62Step1Chunk0_2_checked, root8Node62Step1Chunk0_3_checked, root8Node62Step1Chunk0_4_checked, root8Node62Step1Chunk0_5_checked, root8Node62Step1Chunk1_0_checked, root8Node62Step1Chunk1_1_checked, root8Node62Step1Chunk1_2_checked, root8Node62Step1Chunk1_3_checked, root8Node62Step1Chunk1_4_checked, root8Node62Step1Chunk1_5_checked, root8Node62Step1Chunk2_0_checked, root8Node62Step1Chunk2_1_checked, root8Node62Step1Chunk2_2_checked, root8Node62Step1Chunk2_3_checked, root8Node62Step1Chunk2_4_checked, root8Node62Step1Chunk2_5_checked, root8Node62Step1Chunk3_0_checked, root8Node62Step1Chunk3_1_checked, root8Node62Step1Chunk3_2_checked, root8Node62Step1Chunk3_3_checked, root8Node62Step1Chunk3_4_checked, root8Node62Step1Chunk3_5_checked, root8Node62Step1Chunk4_0_checked, root8Node62Step1Chunk4_1_checked, root8Node62Step1Chunk4_2_checked, root8Node62Step1Chunk4_3_checked, root8Node62Step1Chunk4_4_checked, root8Node62Step1Chunk4_5_checked, root8Node62Step1Chunk5_0_checked, root8Node62Step1Chunk5_1_checked, root8Node62Step1Chunk5_2_checked, root8Node62Step1Chunk5_3_checked, root8Node62Step1Chunk5_4_checked, root8Node62Step1Chunk5_5_checked, root8Node62Step1Chunk6_0_checked, root8Node62Step1Chunk6_1_checked, root8Node62Step1Chunk6_2_checked, root8Node62Step1Chunk6_3_checked, root8Node62Step1Chunk6_4_checked, root8Node62Step1Chunk6_5_checked, root8Node62Step1Chunk7_0_checked, root8Node62Step1Chunk7_1_checked, root8Node62Step1Chunk7_2_checked, root8Node62Step1Chunk7_3_checked, root8Node62Step1Chunk7_4_checked, root8Node62Step1Chunk7_5_checked, root8Node62Step1Chunk8_0_checked, root8Node62Step1Chunk8_1_checked, root8Node62Step1Chunk8_2_checked, root8Node62Step1Chunk8_3_checked, root8Node62Step1Chunk8_4_checked, root8Node62Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node62Step1_checked :
    checkReplacement table33 root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq
    root8Node62Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
