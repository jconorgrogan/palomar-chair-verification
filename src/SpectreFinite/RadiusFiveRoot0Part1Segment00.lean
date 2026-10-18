module

public import SpectreFinite.RadiusFiveRoot0Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node0Domains5 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1),(8,4)]
  | 3 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 7 => [(1,0),(4,0),(7,0),(8,0)]
  | 8 => [(4,3),(7,1),(7,3),(8,3)]
  | 9 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => [(0,1),(1,4),(4,0),(7,4)]
  | 16 => [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 17 => [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 18 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 20 => [(4,0),(7,0),(7,4),(8,0)]
  | 21 => [(0,2),(1,0),(1,5),(4,2),(6,0),(7,0)]
  | 22 => [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 23 => [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 24 => [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 25 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 26 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 27 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 28 => [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 29 => [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => [(1,2),(3,2),(5,2),(5,5),(7,2),(8,2)]
  | 31 => [(4,0),(7,0),(7,4),(8,0)]
  | 32 => [(1,3),(7,3),(8,3)]
  | 33 => [(5,2),(5,5),(8,2)]
  | 34 => [(1,0),(3,0),(5,0)]
  | 35 => [(2,1),(2,5),(4,5)]
  | 36 => [(0,2),(1,0),(6,0),(7,0)]
  | 37 => [(1,1),(4,3),(7,1),(8,3)]
  | 38 => [(4,1),(7,5),(8,5)]
  | 39 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => [(0,3),(0,4),(0,5),(1,1),(6,1),(6,2)]
  | 41 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 42 => [(0,1),(1,4),(6,4),(6,5)]
  | 43 => [(0,4),(0,5),(1,2),(6,2)]
  | 44 => [(4,4),(5,4),(8,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2),(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(6,3),(7,3)]
  | 49 => [(4,2),(5,2),(7,2),(8,2)]
  | 50 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(5,5),(7,5),(8,5)]
  | 53 => [(0,3),(1,0),(6,0),(7,0)]
  | 54 => [(4,3),(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(4,1),(5,1),(8,1)]
  | 58 => [(0,1),(0,2),(6,5)]
  | 59 => [(0,4),(1,1),(6,2)]
  | 60 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => [(0,5),(1,3),(7,3)]
  | 62 => [(4,2),(4,4),(8,2)]
  | 63 => [(1,4),(5,0),(5,3)]
  | 64 => [(0,5),(4,5),(5,5),(8,5)]
  | 65 => [(2,0),(7,0)]
  | 66 => [(7,3),(8,3)]
  | 67 => [(5,2),(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0),(8,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => [(0,4),(1,2),(6,2),(7,1)]
  | 71 => [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 72 => [(0,0),(0,5),(6,0),(6,3)]
  | 73 => [(3,1),(4,4),(7,2)]
  | 74 => [(0,1),(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,2),(6,3)]
  | 76 => [(4,4),(7,2),(8,2),(8,4)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,3),(8,1)]
  | 79 => [(0,2),(1,5),(6,0),(8,2)]
  | 80 => [(1,1),(5,0),(6,1),(7,1)]
  | 81 => [(4,1),(4,5),(7,5),(8,1)]
  | 82 => [(0,2),(1,0),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(6,2),(7,2),(8,5)]
  | 86 => [(2,0),(4,0),(7,0),(8,0),(8,4)]
  | 87 => [(0,0),(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => [(4,0),(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node0Domains5Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1),(8,4)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 7 => some [(1,0),(4,0),(7,0),(8,0)]
  | 8 => some [(4,3),(7,1),(7,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => some [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => some [(0,1),(1,4),(4,0),(7,4)]
  | 16 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 18 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 20 => some [(4,0),(7,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,0),(1,5),(4,2),(6,0),(7,0)]
  | 22 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 24 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 26 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 27 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 28 => some [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,2)]
  | 31 => some [(4,0),(7,0),(7,4),(8,0)]
  | 32 => some [(1,3),(7,3),(8,3)]
  | 33 => some [(5,2),(5,5),(8,2)]
  | 34 => some [(1,0),(3,0),(5,0)]
  | 35 => some [(2,1),(2,5),(4,5)]
  | 36 => some [(0,2),(1,0),(6,0),(7,0)]
  | 37 => some [(1,1),(4,3),(7,1),(8,3)]
  | 38 => some [(4,1),(7,5),(8,5)]
  | 39 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(0,5),(1,1),(6,1),(6,2)]
  | 41 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 42 => some [(0,1),(1,4),(6,4),(6,5)]
  | 43 => some [(0,4),(0,5),(1,2),(6,2)]
  | 44 => some [(4,4),(5,4),(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2),(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(6,3),(7,3)]
  | 49 => some [(4,2),(5,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(5,5),(7,5),(8,5)]
  | 53 => some [(0,3),(1,0),(6,0),(7,0)]
  | 54 => some [(4,3),(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1),(5,1),(8,1)]
  | 58 => some [(0,1),(0,2),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(4,4),(8,2)]
  | 63 => some [(1,4),(5,0),(5,3)]
  | 64 => some [(0,5),(4,5),(5,5),(8,5)]
  | 65 => some [(2,0),(7,0)]
  | 66 => some [(7,3),(8,3)]
  | 67 => some [(5,2),(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 72 => some [(0,0),(0,5),(6,0),(6,3)]
  | 73 => some [(3,1),(4,4),(7,2)]
  | 74 => some [(0,1),(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,2),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,3),(8,1)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(6,2),(7,2),(8,5)]
  | 86 => some [(2,0),(4,0),(7,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node0Domains5_fast_eq : root0Node0Domains5 = expandDomains root0Node0Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node0Domains5 v = expandDomains root0Node0Domains5Fast v from by decide) v
theorem root0Node0Step5Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
