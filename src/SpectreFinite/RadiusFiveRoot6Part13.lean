module

public import SpectreFinite.RadiusFiveRoot6Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable54

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node27Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5),(3,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3),(6,3)]
  | 79 => [(7,2),(8,2)]
  | 80 => [(4,0),(8,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4),(1,1)]
  | 86 => [(5,1),(5,4)]
  | 87 => [(0,1),(6,4)]
  | 88 => [(1,2),(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node27Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5),(3,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node27Domains2_fast_eq : root6Node27Domains2 = expandDomains root6Node27Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node27Domains2 v = expandDomains root6Node27Domains2Fast v from by decide) v
theorem root6Node27Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Narrowing_checked :
    checkNarrowing table54 root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node27Domains1 root6Node27Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node27Step2Chunk0_0_checked, root6Node27Step2Chunk0_1_checked, root6Node27Step2Chunk0_2_checked, root6Node27Step2Chunk0_3_checked, root6Node27Step2Chunk0_4_checked, root6Node27Step2Chunk0_5_checked, root6Node27Step2Chunk1_0_checked, root6Node27Step2Chunk1_1_checked, root6Node27Step2Chunk1_2_checked, root6Node27Step2Chunk1_3_checked, root6Node27Step2Chunk1_4_checked, root6Node27Step2Chunk1_5_checked, root6Node27Step2Chunk2_0_checked, root6Node27Step2Chunk2_1_checked, root6Node27Step2Chunk2_2_checked, root6Node27Step2Chunk2_3_checked, root6Node27Step2Chunk2_4_checked, root6Node27Step2Chunk2_5_checked, root6Node27Step2Chunk3_0_checked, root6Node27Step2Chunk3_1_checked, root6Node27Step2Chunk3_2_checked, root6Node27Step2Chunk3_3_checked, root6Node27Step2Chunk3_4_checked, root6Node27Step2Chunk3_5_checked, root6Node27Step2Chunk4_0_checked, root6Node27Step2Chunk4_1_checked, root6Node27Step2Chunk4_2_checked, root6Node27Step2Chunk4_3_checked, root6Node27Step2Chunk4_4_checked, root6Node27Step2Chunk4_5_checked, root6Node27Step2Chunk5_0_checked, root6Node27Step2Chunk5_1_checked, root6Node27Step2Chunk5_2_checked, root6Node27Step2Chunk5_3_checked, root6Node27Step2Chunk5_4_checked, root6Node27Step2Chunk5_5_checked, root6Node27Step2Chunk6_0_checked, root6Node27Step2Chunk6_1_checked, root6Node27Step2Chunk6_2_checked, root6Node27Step2Chunk6_3_checked, root6Node27Step2Chunk6_4_checked, root6Node27Step2Chunk6_5_checked, root6Node27Step2Chunk7_0_checked, root6Node27Step2Chunk7_1_checked, root6Node27Step2Chunk7_2_checked, root6Node27Step2Chunk7_3_checked, root6Node27Step2Chunk7_4_checked, root6Node27Step2Chunk7_5_checked, root6Node27Step2Chunk8_0_checked, root6Node27Step2Chunk8_1_checked, root6Node27Step2Chunk8_2_checked, root6Node27Step2Chunk8_3_checked, root6Node27Step2Chunk8_4_checked, root6Node27Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node27Step2_checked :
    checkReplacement table54 root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq
    root6Node27Step2Narrowing_checked (by decide)
def root6Node28Domains0 : Domains 91 State := restrict root6Node27Domains2 29 (1,5)
def root6Node28Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node28Domains0_fast_eq : root6Node28Domains0 = expandDomains root6Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node28Domains0 v = expandDomains root6Node28Domains0Fast v from by decide) v
def root6Node28Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3),(6,3)]
  | 79 => [(7,2),(8,2)]
  | 80 => [(4,0),(8,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4),(1,1)]
  | 86 => [(5,1),(5,4)]
  | 87 => [(0,1),(6,4)]
  | 88 => [(1,2),(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node28Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node28Domains1_fast_eq : root6Node28Domains1 = expandDomains root6Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node28Domains1 v = expandDomains root6Node28Domains1Fast v from by decide) v
theorem root6Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Narrowing_checked :
    checkNarrowing table12 root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root6Node28Domains0 root6Node28Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node28Step1Chunk0_0_checked, root6Node28Step1Chunk0_1_checked, root6Node28Step1Chunk0_2_checked, root6Node28Step1Chunk0_3_checked, root6Node28Step1Chunk0_4_checked, root6Node28Step1Chunk0_5_checked, root6Node28Step1Chunk1_0_checked, root6Node28Step1Chunk1_1_checked, root6Node28Step1Chunk1_2_checked, root6Node28Step1Chunk1_3_checked, root6Node28Step1Chunk1_4_checked, root6Node28Step1Chunk1_5_checked, root6Node28Step1Chunk2_0_checked, root6Node28Step1Chunk2_1_checked, root6Node28Step1Chunk2_2_checked, root6Node28Step1Chunk2_3_checked, root6Node28Step1Chunk2_4_checked, root6Node28Step1Chunk2_5_checked, root6Node28Step1Chunk3_0_checked, root6Node28Step1Chunk3_1_checked, root6Node28Step1Chunk3_2_checked, root6Node28Step1Chunk3_3_checked, root6Node28Step1Chunk3_4_checked, root6Node28Step1Chunk3_5_checked, root6Node28Step1Chunk4_0_checked, root6Node28Step1Chunk4_1_checked, root6Node28Step1Chunk4_2_checked, root6Node28Step1Chunk4_3_checked, root6Node28Step1Chunk4_4_checked, root6Node28Step1Chunk4_5_checked, root6Node28Step1Chunk5_0_checked, root6Node28Step1Chunk5_1_checked, root6Node28Step1Chunk5_2_checked, root6Node28Step1Chunk5_3_checked, root6Node28Step1Chunk5_4_checked, root6Node28Step1Chunk5_5_checked, root6Node28Step1Chunk6_0_checked, root6Node28Step1Chunk6_1_checked, root6Node28Step1Chunk6_2_checked, root6Node28Step1Chunk6_3_checked, root6Node28Step1Chunk6_4_checked, root6Node28Step1Chunk6_5_checked, root6Node28Step1Chunk7_0_checked, root6Node28Step1Chunk7_1_checked, root6Node28Step1Chunk7_2_checked, root6Node28Step1Chunk7_3_checked, root6Node28Step1Chunk7_4_checked, root6Node28Step1Chunk7_5_checked, root6Node28Step1Chunk8_0_checked, root6Node28Step1Chunk8_1_checked, root6Node28Step1Chunk8_2_checked, root6Node28Step1Chunk8_3_checked, root6Node28Step1Chunk8_4_checked, root6Node28Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node28Step1_checked :
    checkReplacement table12 root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq
    root6Node28Step1Narrowing_checked (by decide)
def root6Node29Domains0 : Domains 91 State := restrict root6Node28Domains1 78 (1,3)
def root6Node29Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node29Domains0_fast_eq : root6Node29Domains0 = expandDomains root6Node29Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node29Domains0 v = expandDomains root6Node29Domains0Fast v from by decide) v
def root6Node29Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3)]
  | 79 => [(8,2)]
  | 80 => [(8,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4)]
  | 86 => [(5,4)]
  | 87 => [(6,4)]
  | 88 => [(1,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node29Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3)]
  | 79 => some [(8,2)]
  | 80 => some [(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(5,4)]
  | 87 => some [(6,4)]
  | 88 => some [(1,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node29Domains1_fast_eq : root6Node29Domains1 = expandDomains root6Node29Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node29Domains1 v = expandDomains root6Node29Domains1Fast v from by decide) v
theorem root6Node29Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq (by decide)
theorem root6Node29Step1Narrowing_checked :
    checkNarrowing table54 root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node29Domains0 root6Node29Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node29Step1Chunk0_0_checked, root6Node29Step1Chunk0_1_checked, root6Node29Step1Chunk0_2_checked, root6Node29Step1Chunk0_3_checked, root6Node29Step1Chunk0_4_checked, root6Node29Step1Chunk0_5_checked, root6Node29Step1Chunk1_0_checked, root6Node29Step1Chunk1_1_checked, root6Node29Step1Chunk1_2_checked, root6Node29Step1Chunk1_3_checked, root6Node29Step1Chunk1_4_checked, root6Node29Step1Chunk1_5_checked, root6Node29Step1Chunk2_0_checked, root6Node29Step1Chunk2_1_checked, root6Node29Step1Chunk2_2_checked, root6Node29Step1Chunk2_3_checked, root6Node29Step1Chunk2_4_checked, root6Node29Step1Chunk2_5_checked, root6Node29Step1Chunk3_0_checked, root6Node29Step1Chunk3_1_checked, root6Node29Step1Chunk3_2_checked, root6Node29Step1Chunk3_3_checked, root6Node29Step1Chunk3_4_checked, root6Node29Step1Chunk3_5_checked, root6Node29Step1Chunk4_0_checked, root6Node29Step1Chunk4_1_checked, root6Node29Step1Chunk4_2_checked, root6Node29Step1Chunk4_3_checked, root6Node29Step1Chunk4_4_checked, root6Node29Step1Chunk4_5_checked, root6Node29Step1Chunk5_0_checked, root6Node29Step1Chunk5_1_checked, root6Node29Step1Chunk5_2_checked, root6Node29Step1Chunk5_3_checked, root6Node29Step1Chunk5_4_checked, root6Node29Step1Chunk5_5_checked, root6Node29Step1Chunk6_0_checked, root6Node29Step1Chunk6_1_checked, root6Node29Step1Chunk6_2_checked, root6Node29Step1Chunk6_3_checked, root6Node29Step1Chunk6_4_checked, root6Node29Step1Chunk6_5_checked, root6Node29Step1Chunk7_0_checked, root6Node29Step1Chunk7_1_checked, root6Node29Step1Chunk7_2_checked, root6Node29Step1Chunk7_3_checked, root6Node29Step1Chunk7_4_checked, root6Node29Step1Chunk7_5_checked, root6Node29Step1Chunk8_0_checked, root6Node29Step1Chunk8_1_checked, root6Node29Step1Chunk8_2_checked, root6Node29Step1Chunk8_3_checked, root6Node29Step1Chunk8_4_checked, root6Node29Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node29Step1_checked :
    checkReplacement table54 root6Node29Domains0 root6Node29Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node29Domains0 root6Node29Domains1
    root6Node29Domains0Fast root6Node29Domains1Fast
    root6Node29Domains0_fast_eq root6Node29Domains1_fast_eq
    root6Node29Step1Narrowing_checked (by decide)
theorem root6Node29Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node29Domains1 (.output 12) = true := by decide
def root6Node30Domains0 : Domains 91 State := restrict root6Node28Domains1 78 (6,3)
def root6Node30Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node30Domains0_fast_eq : root6Node30Domains0 = expandDomains root6Node30Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node30Domains0 v = expandDomains root6Node30Domains0Fast v from by decide) v
def root6Node30Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1)]
  | 50 => [(0,1)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(4,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(1,1)]
  | 86 => [(5,1)]
  | 87 => [(0,1)]
  | 88 => [(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node30Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1)]
  | 50 => some [(0,1)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(4,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(5,1)]
  | 87 => some [(0,1)]
  | 88 => some [(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node30Domains1_fast_eq : root6Node30Domains1 = expandDomains root6Node30Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node30Domains1 v = expandDomains root6Node30Domains1Fast v from by decide) v
theorem root6Node30Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq (by decide)
theorem root6Node30Step1Narrowing_checked :
    checkNarrowing table54 root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node30Domains0 root6Node30Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node30Step1Chunk0_0_checked, root6Node30Step1Chunk0_1_checked, root6Node30Step1Chunk0_2_checked, root6Node30Step1Chunk0_3_checked, root6Node30Step1Chunk0_4_checked, root6Node30Step1Chunk0_5_checked, root6Node30Step1Chunk1_0_checked, root6Node30Step1Chunk1_1_checked, root6Node30Step1Chunk1_2_checked, root6Node30Step1Chunk1_3_checked, root6Node30Step1Chunk1_4_checked, root6Node30Step1Chunk1_5_checked, root6Node30Step1Chunk2_0_checked, root6Node30Step1Chunk2_1_checked, root6Node30Step1Chunk2_2_checked, root6Node30Step1Chunk2_3_checked, root6Node30Step1Chunk2_4_checked, root6Node30Step1Chunk2_5_checked, root6Node30Step1Chunk3_0_checked, root6Node30Step1Chunk3_1_checked, root6Node30Step1Chunk3_2_checked, root6Node30Step1Chunk3_3_checked, root6Node30Step1Chunk3_4_checked, root6Node30Step1Chunk3_5_checked, root6Node30Step1Chunk4_0_checked, root6Node30Step1Chunk4_1_checked, root6Node30Step1Chunk4_2_checked, root6Node30Step1Chunk4_3_checked, root6Node30Step1Chunk4_4_checked, root6Node30Step1Chunk4_5_checked, root6Node30Step1Chunk5_0_checked, root6Node30Step1Chunk5_1_checked, root6Node30Step1Chunk5_2_checked, root6Node30Step1Chunk5_3_checked, root6Node30Step1Chunk5_4_checked, root6Node30Step1Chunk5_5_checked, root6Node30Step1Chunk6_0_checked, root6Node30Step1Chunk6_1_checked, root6Node30Step1Chunk6_2_checked, root6Node30Step1Chunk6_3_checked, root6Node30Step1Chunk6_4_checked, root6Node30Step1Chunk6_5_checked, root6Node30Step1Chunk7_0_checked, root6Node30Step1Chunk7_1_checked, root6Node30Step1Chunk7_2_checked, root6Node30Step1Chunk7_3_checked, root6Node30Step1Chunk7_4_checked, root6Node30Step1Chunk7_5_checked, root6Node30Step1Chunk8_0_checked, root6Node30Step1Chunk8_1_checked, root6Node30Step1Chunk8_2_checked, root6Node30Step1Chunk8_3_checked, root6Node30Step1Chunk8_4_checked, root6Node30Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node30Step1_checked :
    checkReplacement table54 root6Node30Domains0 root6Node30Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node30Domains0 root6Node30Domains1
    root6Node30Domains0Fast root6Node30Domains1Fast
    root6Node30Domains0_fast_eq root6Node30Domains1_fast_eq
    root6Node30Step1Narrowing_checked (by decide)
theorem root6Node30Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node30Domains1 (.output 13) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
