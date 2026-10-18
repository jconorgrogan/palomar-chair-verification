module

public import SpectreFinite.RadiusFiveRoot1Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node2Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3),(5,3),(8,3)]
  | 5 => [(7,5),(8,5)]
  | 6 => [(0,4),(6,2)]
  | 7 => [(3,4),(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(2,2),(7,2)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(2,1),(2,3)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(0,1),(4,1),(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(0,0),(6,4)]
  | 23 => [(1,2),(3,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3),(8,3)]
  | 29 => [(1,0),(5,2),(5,5)]
  | 30 => [(7,1)]
  | 31 => [(1,5),(7,5)]
  | 32 => [(0,3),(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(1,4),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,0),(4,4),(8,4)]
  | 40 => [(5,0),(8,0)]
  | 41 => [(4,5),(7,3)]
  | 42 => [(4,2),(7,0)]
  | 43 => [(5,3),(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,0),(6,1)]
  | 49 => [(5,1),(7,1),(8,1)]
  | 50 => [(0,1),(1,5)]
  | 51 => [(0,0),(6,4)]
  | 52 => [(1,2),(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0),(8,2)]
  | 59 => [(5,0),(5,3),(8,3)]
  | 60 => [(4,5),(8,5)]
  | 61 => [(0,3),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3)]
  | 70 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1),(8,1)]
  | 77 => [(0,2),(1,5)]
  | 78 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => [(3,2),(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(4,3),(6,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,1),(6,2),(6,3)]
def root1Node2Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3),(5,3),(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4),(6,2)]
  | 7 => some [(3,4),(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(1,4),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,0),(6,1)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5)]
  | 51 => some [(0,0),(6,4)]
  | 52 => some [(1,2),(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(8,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(0,3),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3)]
  | 70 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1),(8,1)]
  | 77 => some [(0,2),(1,5)]
  | 78 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node2Domains2_fast_eq : root1Node2Domains2 = expandDomains root1Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node2Domains2 v = expandDomains root1Node2Domains2Fast v from by decide) v
theorem root1Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq (by decide)
theorem root1Node2Step2Narrowing_checked :
    checkNarrowing table57 root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root1Node2Domains1 root1Node2Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node2Step2Chunk0_0_checked, root1Node2Step2Chunk0_1_checked, root1Node2Step2Chunk0_2_checked, root1Node2Step2Chunk0_3_checked, root1Node2Step2Chunk0_4_checked, root1Node2Step2Chunk0_5_checked, root1Node2Step2Chunk1_0_checked, root1Node2Step2Chunk1_1_checked, root1Node2Step2Chunk1_2_checked, root1Node2Step2Chunk1_3_checked, root1Node2Step2Chunk1_4_checked, root1Node2Step2Chunk1_5_checked, root1Node2Step2Chunk2_0_checked, root1Node2Step2Chunk2_1_checked, root1Node2Step2Chunk2_2_checked, root1Node2Step2Chunk2_3_checked, root1Node2Step2Chunk2_4_checked, root1Node2Step2Chunk2_5_checked, root1Node2Step2Chunk3_0_checked, root1Node2Step2Chunk3_1_checked, root1Node2Step2Chunk3_2_checked, root1Node2Step2Chunk3_3_checked, root1Node2Step2Chunk3_4_checked, root1Node2Step2Chunk3_5_checked, root1Node2Step2Chunk4_0_checked, root1Node2Step2Chunk4_1_checked, root1Node2Step2Chunk4_2_checked, root1Node2Step2Chunk4_3_checked, root1Node2Step2Chunk4_4_checked, root1Node2Step2Chunk4_5_checked, root1Node2Step2Chunk5_0_checked, root1Node2Step2Chunk5_1_checked, root1Node2Step2Chunk5_2_checked, root1Node2Step2Chunk5_3_checked, root1Node2Step2Chunk5_4_checked, root1Node2Step2Chunk5_5_checked, root1Node2Step2Chunk6_0_checked, root1Node2Step2Chunk6_1_checked, root1Node2Step2Chunk6_2_checked, root1Node2Step2Chunk6_3_checked, root1Node2Step2Chunk6_4_checked, root1Node2Step2Chunk6_5_checked, root1Node2Step2Chunk7_0_checked, root1Node2Step2Chunk7_1_checked, root1Node2Step2Chunk7_2_checked, root1Node2Step2Chunk7_3_checked, root1Node2Step2Chunk7_4_checked, root1Node2Step2Chunk7_5_checked, root1Node2Step2Chunk8_0_checked, root1Node2Step2Chunk8_1_checked, root1Node2Step2Chunk8_2_checked, root1Node2Step2Chunk8_3_checked, root1Node2Step2Chunk8_4_checked, root1Node2Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node2Step2_checked :
    checkReplacement table57 root1Node2Domains1 root1Node2Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node2Domains1 root1Node2Domains2
    root1Node2Domains1Fast root1Node2Domains2Fast
    root1Node2Domains1_fast_eq root1Node2Domains2_fast_eq
    root1Node2Step2Narrowing_checked (by decide)
def root1Node2Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3),(5,3),(8,3)]
  | 5 => [(7,5),(8,5)]
  | 6 => [(0,4),(6,2)]
  | 7 => [(3,4),(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(2,2),(7,2)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(2,1),(2,3)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(0,1),(4,1),(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(0,0),(6,4)]
  | 23 => [(1,2),(3,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3),(8,3)]
  | 29 => [(1,0),(5,2),(5,5)]
  | 30 => [(7,1)]
  | 31 => [(1,5),(7,5)]
  | 32 => [(0,3),(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(1,4),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,0),(4,4),(8,4)]
  | 40 => [(5,0),(8,0)]
  | 41 => [(4,5),(7,3)]
  | 42 => [(4,2),(7,0)]
  | 43 => [(5,3),(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,0),(6,1)]
  | 49 => [(5,1),(7,1),(8,1)]
  | 50 => [(0,1),(1,5)]
  | 51 => [(0,0),(6,4)]
  | 52 => [(1,2),(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0),(8,2)]
  | 59 => [(5,0),(5,3),(8,3)]
  | 60 => [(4,5),(8,5)]
  | 61 => [(0,3),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3)]
  | 70 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1),(8,1)]
  | 77 => [(0,2),(1,5)]
  | 78 => [(0,4),(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => [(3,2),(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(4,3),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,1),(6,2),(6,3)]
def root1Node2Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3),(5,3),(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4),(6,2)]
  | 7 => some [(3,4),(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(1,4),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,0),(6,1)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5)]
  | 51 => some [(0,0),(6,4)]
  | 52 => some [(1,2),(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(8,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(0,3),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3)]
  | 70 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1),(8,1)]
  | 77 => some [(0,2),(1,5)]
  | 78 => some [(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node2Domains3_fast_eq : root1Node2Domains3 = expandDomains root1Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node2Domains3 v = expandDomains root1Node2Domains3Fast v from by decide) v
theorem root1Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq (by decide)
theorem root1Node2Step3Narrowing_checked :
    checkNarrowing table51 root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root1Node2Domains2 root1Node2Domains3 (by
      simp only [List.all_cons, List.all_nil, root1Node2Step3Chunk0_0_checked, root1Node2Step3Chunk0_1_checked, root1Node2Step3Chunk0_2_checked, root1Node2Step3Chunk0_3_checked, root1Node2Step3Chunk0_4_checked, root1Node2Step3Chunk0_5_checked, root1Node2Step3Chunk1_0_checked, root1Node2Step3Chunk1_1_checked, root1Node2Step3Chunk1_2_checked, root1Node2Step3Chunk1_3_checked, root1Node2Step3Chunk1_4_checked, root1Node2Step3Chunk1_5_checked, root1Node2Step3Chunk2_0_checked, root1Node2Step3Chunk2_1_checked, root1Node2Step3Chunk2_2_checked, root1Node2Step3Chunk2_3_checked, root1Node2Step3Chunk2_4_checked, root1Node2Step3Chunk2_5_checked, root1Node2Step3Chunk3_0_checked, root1Node2Step3Chunk3_1_checked, root1Node2Step3Chunk3_2_checked, root1Node2Step3Chunk3_3_checked, root1Node2Step3Chunk3_4_checked, root1Node2Step3Chunk3_5_checked, root1Node2Step3Chunk4_0_checked, root1Node2Step3Chunk4_1_checked, root1Node2Step3Chunk4_2_checked, root1Node2Step3Chunk4_3_checked, root1Node2Step3Chunk4_4_checked, root1Node2Step3Chunk4_5_checked, root1Node2Step3Chunk5_0_checked, root1Node2Step3Chunk5_1_checked, root1Node2Step3Chunk5_2_checked, root1Node2Step3Chunk5_3_checked, root1Node2Step3Chunk5_4_checked, root1Node2Step3Chunk5_5_checked, root1Node2Step3Chunk6_0_checked, root1Node2Step3Chunk6_1_checked, root1Node2Step3Chunk6_2_checked, root1Node2Step3Chunk6_3_checked, root1Node2Step3Chunk6_4_checked, root1Node2Step3Chunk6_5_checked, root1Node2Step3Chunk7_0_checked, root1Node2Step3Chunk7_1_checked, root1Node2Step3Chunk7_2_checked, root1Node2Step3Chunk7_3_checked, root1Node2Step3Chunk7_4_checked, root1Node2Step3Chunk7_5_checked, root1Node2Step3Chunk8_0_checked, root1Node2Step3Chunk8_1_checked, root1Node2Step3Chunk8_2_checked, root1Node2Step3Chunk8_3_checked, root1Node2Step3Chunk8_4_checked, root1Node2Step3Chunk8_5_checked, Bool.true_and])
theorem root1Node2Step3_checked :
    checkReplacement table51 root1Node2Domains2 root1Node2Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root1Node2Domains2 root1Node2Domains3
    root1Node2Domains2Fast root1Node2Domains3Fast
    root1Node2Domains2_fast_eq root1Node2Domains3_fast_eq
    root1Node2Step3Narrowing_checked (by decide)
def root1Node2Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3),(8,3)]
  | 5 => [(7,5),(8,5)]
  | 6 => [(0,4),(6,2)]
  | 7 => [(3,4),(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(2,2),(7,2)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(2,1),(2,3)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(0,1),(4,1),(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(0,0),(6,4)]
  | 23 => [(1,2),(3,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3),(8,3)]
  | 29 => [(1,0),(5,2),(5,5)]
  | 30 => [(7,1)]
  | 31 => [(1,5),(7,5)]
  | 32 => [(0,3),(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0),(1,4),(6,4)]
  | 38 => [(0,5),(1,2),(7,2)]
  | 39 => [(4,0),(4,4),(8,4)]
  | 40 => [(5,0),(8,0)]
  | 41 => [(4,5),(7,3)]
  | 42 => [(4,2),(7,0)]
  | 43 => [(5,3),(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5),(7,5)]
  | 48 => [(0,3),(6,0),(6,1)]
  | 49 => [(5,1),(7,1),(8,1)]
  | 50 => [(0,1),(1,5)]
  | 51 => [(0,0),(6,4)]
  | 52 => [(1,2),(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(4,2),(7,0),(8,2)]
  | 59 => [(5,0),(5,3),(8,3)]
  | 60 => [(4,5),(8,5)]
  | 61 => [(0,3),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,0),(0,1),(6,4)]
  | 67 => [(1,2),(6,2),(7,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3)]
  | 70 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(1,5),(3,5),(5,5),(7,5)]
  | 75 => [(0,3),(1,0),(6,1)]
  | 76 => [(2,1),(4,1),(8,1)]
  | 77 => [(0,2),(1,5)]
  | 78 => [(0,4),(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => [(3,2),(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(4,3),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,1),(6,2),(6,3)]
def root1Node2Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3),(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4),(6,2)]
  | 7 => some [(3,4),(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(1,4),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,0),(6,1)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5)]
  | 51 => some [(0,0),(6,4)]
  | 52 => some [(1,2),(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(8,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(0,3),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3)]
  | 70 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1),(8,1)]
  | 77 => some [(0,2),(1,5)]
  | 78 => some [(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node2Domains4_fast_eq : root1Node2Domains4 = expandDomains root1Node2Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node2Domains4 v = expandDomains root1Node2Domains4Fast v from by decide) v
theorem root1Node2Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq (by decide)
theorem root1Node2Step4Narrowing_checked :
    checkNarrowing table0 root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root1Node2Domains3 root1Node2Domains4 (by
      simp only [List.all_cons, List.all_nil, root1Node2Step4Chunk0_0_checked, root1Node2Step4Chunk0_1_checked, root1Node2Step4Chunk0_2_checked, root1Node2Step4Chunk0_3_checked, root1Node2Step4Chunk0_4_checked, root1Node2Step4Chunk0_5_checked, root1Node2Step4Chunk1_0_checked, root1Node2Step4Chunk1_1_checked, root1Node2Step4Chunk1_2_checked, root1Node2Step4Chunk1_3_checked, root1Node2Step4Chunk1_4_checked, root1Node2Step4Chunk1_5_checked, root1Node2Step4Chunk2_0_checked, root1Node2Step4Chunk2_1_checked, root1Node2Step4Chunk2_2_checked, root1Node2Step4Chunk2_3_checked, root1Node2Step4Chunk2_4_checked, root1Node2Step4Chunk2_5_checked, root1Node2Step4Chunk3_0_checked, root1Node2Step4Chunk3_1_checked, root1Node2Step4Chunk3_2_checked, root1Node2Step4Chunk3_3_checked, root1Node2Step4Chunk3_4_checked, root1Node2Step4Chunk3_5_checked, root1Node2Step4Chunk4_0_checked, root1Node2Step4Chunk4_1_checked, root1Node2Step4Chunk4_2_checked, root1Node2Step4Chunk4_3_checked, root1Node2Step4Chunk4_4_checked, root1Node2Step4Chunk4_5_checked, root1Node2Step4Chunk5_0_checked, root1Node2Step4Chunk5_1_checked, root1Node2Step4Chunk5_2_checked, root1Node2Step4Chunk5_3_checked, root1Node2Step4Chunk5_4_checked, root1Node2Step4Chunk5_5_checked, root1Node2Step4Chunk6_0_checked, root1Node2Step4Chunk6_1_checked, root1Node2Step4Chunk6_2_checked, root1Node2Step4Chunk6_3_checked, root1Node2Step4Chunk6_4_checked, root1Node2Step4Chunk6_5_checked, root1Node2Step4Chunk7_0_checked, root1Node2Step4Chunk7_1_checked, root1Node2Step4Chunk7_2_checked, root1Node2Step4Chunk7_3_checked, root1Node2Step4Chunk7_4_checked, root1Node2Step4Chunk7_5_checked, root1Node2Step4Chunk8_0_checked, root1Node2Step4Chunk8_1_checked, root1Node2Step4Chunk8_2_checked, root1Node2Step4Chunk8_3_checked, root1Node2Step4Chunk8_4_checked, root1Node2Step4Chunk8_5_checked, Bool.true_and])
theorem root1Node2Step4_checked :
    checkReplacement table0 root1Node2Domains3 root1Node2Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root1Node2Domains3 root1Node2Domains4
    root1Node2Domains3Fast root1Node2Domains4Fast
    root1Node2Domains3_fast_eq root1Node2Domains4_fast_eq
    root1Node2Step4Narrowing_checked (by decide)
def root1Node3Domains0 : Domains 91 State := restrict root1Node2Domains4 4 (4,3)
def root1Node3Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4),(6,2)]
  | 7 => some [(3,4),(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(1,4),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,0),(6,1)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5)]
  | 51 => some [(0,0),(6,4)]
  | 52 => some [(1,2),(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(8,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(0,3),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3)]
  | 70 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1),(8,1)]
  | 77 => some [(0,2),(1,5)]
  | 78 => some [(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node3Domains0_fast_eq : root1Node3Domains0 = expandDomains root1Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node3Domains0 v = expandDomains root1Node3Domains0Fast v from by decide) v
def root1Node3Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(0,4),(6,2)]
  | 7 => [(3,4),(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(2,2)]
  | 13 => [(1,0),(7,0)]
  | 14 => [(2,1),(2,3)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(0,1)]
  | 21 => [(4,4)]
  | 22 => [(0,0),(6,4)]
  | 23 => [(1,2),(3,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(5,0)]
  | 28 => [(4,5)]
  | 29 => [(1,0)]
  | 30 => [(7,1)]
  | 31 => [(1,5),(7,5)]
  | 32 => [(0,3),(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(5,0),(8,0)]
  | 41 => [(4,5),(7,3)]
  | 42 => [(4,2),(7,0)]
  | 43 => [(5,3),(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0),(6,4)]
  | 52 => [(1,2),(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(0,3),(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(6,3)]
  | 70 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(4,1)]
  | 77 => [(0,2)]
  | 78 => [(0,4),(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => [(3,2),(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(4,3),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,1),(6,2),(6,3)]
def root1Node3Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(0,4),(6,2)]
  | 7 => some [(3,4),(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(5,0)]
  | 28 => some [(4,5)]
  | 29 => some [(1,0)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0),(6,4)]
  | 52 => some [(1,2),(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,3),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(6,3)]
  | 70 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(4,1)]
  | 77 => some [(0,2)]
  | 78 => some [(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node3Domains1_fast_eq : root1Node3Domains1 = expandDomains root1Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node3Domains1 v = expandDomains root1Node3Domains1Fast v from by decide) v
theorem root1Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq (by decide)
theorem root1Node3Step1Narrowing_checked :
    checkNarrowing table36 root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root1Node3Domains0 root1Node3Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node3Step1Chunk0_0_checked, root1Node3Step1Chunk0_1_checked, root1Node3Step1Chunk0_2_checked, root1Node3Step1Chunk0_3_checked, root1Node3Step1Chunk0_4_checked, root1Node3Step1Chunk0_5_checked, root1Node3Step1Chunk1_0_checked, root1Node3Step1Chunk1_1_checked, root1Node3Step1Chunk1_2_checked, root1Node3Step1Chunk1_3_checked, root1Node3Step1Chunk1_4_checked, root1Node3Step1Chunk1_5_checked, root1Node3Step1Chunk2_0_checked, root1Node3Step1Chunk2_1_checked, root1Node3Step1Chunk2_2_checked, root1Node3Step1Chunk2_3_checked, root1Node3Step1Chunk2_4_checked, root1Node3Step1Chunk2_5_checked, root1Node3Step1Chunk3_0_checked, root1Node3Step1Chunk3_1_checked, root1Node3Step1Chunk3_2_checked, root1Node3Step1Chunk3_3_checked, root1Node3Step1Chunk3_4_checked, root1Node3Step1Chunk3_5_checked, root1Node3Step1Chunk4_0_checked, root1Node3Step1Chunk4_1_checked, root1Node3Step1Chunk4_2_checked, root1Node3Step1Chunk4_3_checked, root1Node3Step1Chunk4_4_checked, root1Node3Step1Chunk4_5_checked, root1Node3Step1Chunk5_0_checked, root1Node3Step1Chunk5_1_checked, root1Node3Step1Chunk5_2_checked, root1Node3Step1Chunk5_3_checked, root1Node3Step1Chunk5_4_checked, root1Node3Step1Chunk5_5_checked, root1Node3Step1Chunk6_0_checked, root1Node3Step1Chunk6_1_checked, root1Node3Step1Chunk6_2_checked, root1Node3Step1Chunk6_3_checked, root1Node3Step1Chunk6_4_checked, root1Node3Step1Chunk6_5_checked, root1Node3Step1Chunk7_0_checked, root1Node3Step1Chunk7_1_checked, root1Node3Step1Chunk7_2_checked, root1Node3Step1Chunk7_3_checked, root1Node3Step1Chunk7_4_checked, root1Node3Step1Chunk7_5_checked, root1Node3Step1Chunk8_0_checked, root1Node3Step1Chunk8_1_checked, root1Node3Step1Chunk8_2_checked, root1Node3Step1Chunk8_3_checked, root1Node3Step1Chunk8_4_checked, root1Node3Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node3Step1_checked :
    checkReplacement table36 root1Node3Domains0 root1Node3Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node3Domains0 root1Node3Domains1
    root1Node3Domains0Fast root1Node3Domains1Fast
    root1Node3Domains0_fast_eq root1Node3Domains1_fast_eq
    root1Node3Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
