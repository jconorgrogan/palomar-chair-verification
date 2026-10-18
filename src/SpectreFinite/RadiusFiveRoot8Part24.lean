module

public import SpectreFinite.RadiusFiveRoot8Part23
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node60Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(1,3),(6,3)]
  | 5 => [(4,2),(4,4),(7,2),(8,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0)]
  | 8 => [(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5),(8,1)]
  | 10 => [(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(7,1)]
  | 12 => [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(2,3),(4,3),(7,3),(8,3)]
  | 20 => [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => [(4,4),(5,1),(5,4),(8,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => [(2,5),(4,5),(7,3),(8,5)]
  | 31 => [(1,0),(4,2),(6,0),(7,0)]
  | 32 => [(4,3),(5,3),(7,1),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(4,2),(7,0),(8,0),(8,2)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | _ => [(0,3),(1,1),(4,3),(6,1),(7,1)]
def root8Node60Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3)]
  | 5 => some [(4,2),(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0)]
  | 8 => some [(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(7,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => some [(4,4),(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => some [(2,5),(4,5),(7,3),(8,5)]
  | 31 => some [(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(4,2),(7,0),(8,0),(8,2)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | _ => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
theorem root8Node60Domains2_fast_eq : root8Node60Domains2 = expandDomains root8Node60Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node60Domains2 v = expandDomains root8Node60Domains2Fast v from by decide) v
theorem root8Node60Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Narrowing_checked :
    checkNarrowing table54 root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node60Domains1 root8Node60Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node60Step2Chunk0_0_checked, root8Node60Step2Chunk0_1_checked, root8Node60Step2Chunk0_2_checked, root8Node60Step2Chunk0_3_checked, root8Node60Step2Chunk0_4_checked, root8Node60Step2Chunk0_5_checked, root8Node60Step2Chunk1_0_checked, root8Node60Step2Chunk1_1_checked, root8Node60Step2Chunk1_2_checked, root8Node60Step2Chunk1_3_checked, root8Node60Step2Chunk1_4_checked, root8Node60Step2Chunk1_5_checked, root8Node60Step2Chunk2_0_checked, root8Node60Step2Chunk2_1_checked, root8Node60Step2Chunk2_2_checked, root8Node60Step2Chunk2_3_checked, root8Node60Step2Chunk2_4_checked, root8Node60Step2Chunk2_5_checked, root8Node60Step2Chunk3_0_checked, root8Node60Step2Chunk3_1_checked, root8Node60Step2Chunk3_2_checked, root8Node60Step2Chunk3_3_checked, root8Node60Step2Chunk3_4_checked, root8Node60Step2Chunk3_5_checked, root8Node60Step2Chunk4_0_checked, root8Node60Step2Chunk4_1_checked, root8Node60Step2Chunk4_2_checked, root8Node60Step2Chunk4_3_checked, root8Node60Step2Chunk4_4_checked, root8Node60Step2Chunk4_5_checked, root8Node60Step2Chunk5_0_checked, root8Node60Step2Chunk5_1_checked, root8Node60Step2Chunk5_2_checked, root8Node60Step2Chunk5_3_checked, root8Node60Step2Chunk5_4_checked, root8Node60Step2Chunk5_5_checked, root8Node60Step2Chunk6_0_checked, root8Node60Step2Chunk6_1_checked, root8Node60Step2Chunk6_2_checked, root8Node60Step2Chunk6_3_checked, root8Node60Step2Chunk6_4_checked, root8Node60Step2Chunk6_5_checked, root8Node60Step2Chunk7_0_checked, root8Node60Step2Chunk7_1_checked, root8Node60Step2Chunk7_2_checked, root8Node60Step2Chunk7_3_checked, root8Node60Step2Chunk7_4_checked, root8Node60Step2Chunk7_5_checked, root8Node60Step2Chunk8_0_checked, root8Node60Step2Chunk8_1_checked, root8Node60Step2Chunk8_2_checked, root8Node60Step2Chunk8_3_checked, root8Node60Step2Chunk8_4_checked, root8Node60Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node60Step2_checked :
    checkReplacement table54 root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq
    root8Node60Step2Narrowing_checked (by decide)
def root8Node60Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(1,3),(6,3)]
  | 5 => [(4,2),(4,4),(7,2),(8,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0)]
  | 8 => [(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5),(8,1)]
  | 10 => [(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(7,1)]
  | 12 => [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(2,3),(4,3),(7,3),(8,3)]
  | 20 => [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => [(4,4),(5,1),(5,4),(8,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => [(2,5),(4,5),(7,3),(8,5)]
  | 31 => [(1,0),(4,2),(6,0),(7,0)]
  | 32 => [(4,3),(5,3),(7,1),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node60Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3)]
  | 5 => some [(4,2),(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0)]
  | 8 => some [(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(7,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => some [(4,4),(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => some [(2,5),(4,5),(7,3),(8,5)]
  | 31 => some [(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node60Domains3_fast_eq : root8Node60Domains3 = expandDomains root8Node60Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node60Domains3 v = expandDomains root8Node60Domains3Fast v from by decide) v
theorem root8Node60Step3Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq (by decide)
theorem root8Node60Step3Narrowing_checked :
    checkNarrowing table57 root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root8Node60Domains2 root8Node60Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node60Step3Chunk0_0_checked, root8Node60Step3Chunk0_1_checked, root8Node60Step3Chunk0_2_checked, root8Node60Step3Chunk0_3_checked, root8Node60Step3Chunk0_4_checked, root8Node60Step3Chunk0_5_checked, root8Node60Step3Chunk1_0_checked, root8Node60Step3Chunk1_1_checked, root8Node60Step3Chunk1_2_checked, root8Node60Step3Chunk1_3_checked, root8Node60Step3Chunk1_4_checked, root8Node60Step3Chunk1_5_checked, root8Node60Step3Chunk2_0_checked, root8Node60Step3Chunk2_1_checked, root8Node60Step3Chunk2_2_checked, root8Node60Step3Chunk2_3_checked, root8Node60Step3Chunk2_4_checked, root8Node60Step3Chunk2_5_checked, root8Node60Step3Chunk3_0_checked, root8Node60Step3Chunk3_1_checked, root8Node60Step3Chunk3_2_checked, root8Node60Step3Chunk3_3_checked, root8Node60Step3Chunk3_4_checked, root8Node60Step3Chunk3_5_checked, root8Node60Step3Chunk4_0_checked, root8Node60Step3Chunk4_1_checked, root8Node60Step3Chunk4_2_checked, root8Node60Step3Chunk4_3_checked, root8Node60Step3Chunk4_4_checked, root8Node60Step3Chunk4_5_checked, root8Node60Step3Chunk5_0_checked, root8Node60Step3Chunk5_1_checked, root8Node60Step3Chunk5_2_checked, root8Node60Step3Chunk5_3_checked, root8Node60Step3Chunk5_4_checked, root8Node60Step3Chunk5_5_checked, root8Node60Step3Chunk6_0_checked, root8Node60Step3Chunk6_1_checked, root8Node60Step3Chunk6_2_checked, root8Node60Step3Chunk6_3_checked, root8Node60Step3Chunk6_4_checked, root8Node60Step3Chunk6_5_checked, root8Node60Step3Chunk7_0_checked, root8Node60Step3Chunk7_1_checked, root8Node60Step3Chunk7_2_checked, root8Node60Step3Chunk7_3_checked, root8Node60Step3Chunk7_4_checked, root8Node60Step3Chunk7_5_checked, root8Node60Step3Chunk8_0_checked, root8Node60Step3Chunk8_1_checked, root8Node60Step3Chunk8_2_checked, root8Node60Step3Chunk8_3_checked, root8Node60Step3Chunk8_4_checked, root8Node60Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node60Step3_checked :
    checkReplacement table57 root8Node60Domains2 root8Node60Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node60Domains2 root8Node60Domains3
    root8Node60Domains2Fast root8Node60Domains3Fast
    root8Node60Domains2_fast_eq root8Node60Domains3_fast_eq
    root8Node60Step3Narrowing_checked (by decide)
def root8Node60Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(1,3),(6,3)]
  | 5 => [(4,2),(4,4),(7,2),(8,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0)]
  | 8 => [(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5),(8,1)]
  | 10 => [(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(7,1)]
  | 12 => [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(2,3),(4,3),(7,3),(8,3)]
  | 20 => [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => [(4,4),(5,1),(5,4),(8,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => [(2,5),(4,5),(7,3),(8,5)]
  | 31 => [(1,0),(4,2),(6,0),(7,0)]
  | 32 => [(4,3),(5,3),(7,1),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node60Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3)]
  | 5 => some [(4,2),(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0)]
  | 8 => some [(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(7,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => some [(4,4),(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => some [(2,5),(4,5),(7,3),(8,5)]
  | 31 => some [(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node60Domains4_fast_eq : root8Node60Domains4 = expandDomains root8Node60Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node60Domains4 v = expandDomains root8Node60Domains4Fast v from by decide) v
theorem root8Node60Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq (by decide)
theorem root8Node60Step4Narrowing_checked :
    checkNarrowing table0 root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root8Node60Domains3 root8Node60Domains4 (by
      simp only [List.all_cons, List.all_nil, root8Node60Step4Chunk0_0_checked, root8Node60Step4Chunk0_1_checked, root8Node60Step4Chunk0_2_checked, root8Node60Step4Chunk0_3_checked, root8Node60Step4Chunk0_4_checked, root8Node60Step4Chunk0_5_checked, root8Node60Step4Chunk1_0_checked, root8Node60Step4Chunk1_1_checked, root8Node60Step4Chunk1_2_checked, root8Node60Step4Chunk1_3_checked, root8Node60Step4Chunk1_4_checked, root8Node60Step4Chunk1_5_checked, root8Node60Step4Chunk2_0_checked, root8Node60Step4Chunk2_1_checked, root8Node60Step4Chunk2_2_checked, root8Node60Step4Chunk2_3_checked, root8Node60Step4Chunk2_4_checked, root8Node60Step4Chunk2_5_checked, root8Node60Step4Chunk3_0_checked, root8Node60Step4Chunk3_1_checked, root8Node60Step4Chunk3_2_checked, root8Node60Step4Chunk3_3_checked, root8Node60Step4Chunk3_4_checked, root8Node60Step4Chunk3_5_checked, root8Node60Step4Chunk4_0_checked, root8Node60Step4Chunk4_1_checked, root8Node60Step4Chunk4_2_checked, root8Node60Step4Chunk4_3_checked, root8Node60Step4Chunk4_4_checked, root8Node60Step4Chunk4_5_checked, root8Node60Step4Chunk5_0_checked, root8Node60Step4Chunk5_1_checked, root8Node60Step4Chunk5_2_checked, root8Node60Step4Chunk5_3_checked, root8Node60Step4Chunk5_4_checked, root8Node60Step4Chunk5_5_checked, root8Node60Step4Chunk6_0_checked, root8Node60Step4Chunk6_1_checked, root8Node60Step4Chunk6_2_checked, root8Node60Step4Chunk6_3_checked, root8Node60Step4Chunk6_4_checked, root8Node60Step4Chunk6_5_checked, root8Node60Step4Chunk7_0_checked, root8Node60Step4Chunk7_1_checked, root8Node60Step4Chunk7_2_checked, root8Node60Step4Chunk7_3_checked, root8Node60Step4Chunk7_4_checked, root8Node60Step4Chunk7_5_checked, root8Node60Step4Chunk8_0_checked, root8Node60Step4Chunk8_1_checked, root8Node60Step4Chunk8_2_checked, root8Node60Step4Chunk8_3_checked, root8Node60Step4Chunk8_4_checked, root8Node60Step4Chunk8_5_checked, Bool.true_and])
theorem root8Node60Step4_checked :
    checkReplacement table0 root8Node60Domains3 root8Node60Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root8Node60Domains3 root8Node60Domains4
    root8Node60Domains3Fast root8Node60Domains4Fast
    root8Node60Domains3_fast_eq root8Node60Domains4_fast_eq
    root8Node60Step4Narrowing_checked (by decide)
def root8Node61Domains0 : Domains 91 State := restrict root8Node60Domains4 3 (1,4)
def root8Node61Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5),(1,3),(6,3)]
  | 5 => some [(4,2),(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0)]
  | 8 => some [(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(7,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(0,1),(1,4),(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => some [(4,4),(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => some [(2,5),(4,5),(7,3),(8,5)]
  | 31 => some [(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node61Domains0_fast_eq : root8Node61Domains0 = expandDomains root8Node61Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node61Domains0 v = expandDomains root8Node61Domains0Fast v from by decide) v
def root8Node61Domains1 (v : Fin 91) : List State :=
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
  | 52 => [(5,1),(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node61Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node61Domains1_fast_eq : root8Node61Domains1 = expandDomains root8Node61Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node61Domains1 v = expandDomains root8Node61Domains1Fast v from by decide) v
theorem root8Node61Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Narrowing_checked :
    checkNarrowing table25 root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root8Node61Domains0 root8Node61Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node61Step1Chunk0_0_checked, root8Node61Step1Chunk0_1_checked, root8Node61Step1Chunk0_2_checked, root8Node61Step1Chunk0_3_checked, root8Node61Step1Chunk0_4_checked, root8Node61Step1Chunk0_5_checked, root8Node61Step1Chunk1_0_checked, root8Node61Step1Chunk1_1_checked, root8Node61Step1Chunk1_2_checked, root8Node61Step1Chunk1_3_checked, root8Node61Step1Chunk1_4_checked, root8Node61Step1Chunk1_5_checked, root8Node61Step1Chunk2_0_checked, root8Node61Step1Chunk2_1_checked, root8Node61Step1Chunk2_2_checked, root8Node61Step1Chunk2_3_checked, root8Node61Step1Chunk2_4_checked, root8Node61Step1Chunk2_5_checked, root8Node61Step1Chunk3_0_checked, root8Node61Step1Chunk3_1_checked, root8Node61Step1Chunk3_2_checked, root8Node61Step1Chunk3_3_checked, root8Node61Step1Chunk3_4_checked, root8Node61Step1Chunk3_5_checked, root8Node61Step1Chunk4_0_checked, root8Node61Step1Chunk4_1_checked, root8Node61Step1Chunk4_2_checked, root8Node61Step1Chunk4_3_checked, root8Node61Step1Chunk4_4_checked, root8Node61Step1Chunk4_5_checked, root8Node61Step1Chunk5_0_checked, root8Node61Step1Chunk5_1_checked, root8Node61Step1Chunk5_2_checked, root8Node61Step1Chunk5_3_checked, root8Node61Step1Chunk5_4_checked, root8Node61Step1Chunk5_5_checked, root8Node61Step1Chunk6_0_checked, root8Node61Step1Chunk6_1_checked, root8Node61Step1Chunk6_2_checked, root8Node61Step1Chunk6_3_checked, root8Node61Step1Chunk6_4_checked, root8Node61Step1Chunk6_5_checked, root8Node61Step1Chunk7_0_checked, root8Node61Step1Chunk7_1_checked, root8Node61Step1Chunk7_2_checked, root8Node61Step1Chunk7_3_checked, root8Node61Step1Chunk7_4_checked, root8Node61Step1Chunk7_5_checked, root8Node61Step1Chunk8_0_checked, root8Node61Step1Chunk8_1_checked, root8Node61Step1Chunk8_2_checked, root8Node61Step1Chunk8_3_checked, root8Node61Step1Chunk8_4_checked, root8Node61Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node61Step1_checked :
    checkReplacement table25 root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq
    root8Node61Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
