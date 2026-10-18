module

public import SpectreFinite.RadiusFiveRoot5Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable10
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable13

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node1Domains5 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(4,0),(7,4)]
  | 4 => [(0,5),(1,3),(6,3),(7,3)]
  | 5 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => [(0,2),(1,0),(6,0)]
  | 8 => [(1,1),(7,1)]
  | 9 => [(4,1),(5,1),(7,5),(8,1)]
  | 10 => [(0,1),(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2),(7,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0),(7,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0),(7,4)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1),(8,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node1Domains5Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(4,0),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => some [(0,2),(1,0),(6,0)]
  | 8 => some [(1,1),(7,1)]
  | 9 => some [(4,1),(5,1),(7,5),(8,1)]
  | 10 => some [(0,1),(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2),(7,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node1Domains5_fast_eq : root5Node1Domains5 = expandDomains root5Node1Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node1Domains5 v = expandDomains root5Node1Domains5Fast v from by decide) v
theorem root5Node1Step5Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq (by decide)
theorem root5Node1Step5Narrowing_checked :
    checkNarrowing table1 root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root5Node1Domains4 root5Node1Domains5 (by
      simp only [List.all_cons, List.all_nil, root5Node1Step5Chunk0_0_checked, root5Node1Step5Chunk0_1_checked, root5Node1Step5Chunk0_2_checked, root5Node1Step5Chunk0_3_checked, root5Node1Step5Chunk0_4_checked, root5Node1Step5Chunk0_5_checked, root5Node1Step5Chunk1_0_checked, root5Node1Step5Chunk1_1_checked, root5Node1Step5Chunk1_2_checked, root5Node1Step5Chunk1_3_checked, root5Node1Step5Chunk1_4_checked, root5Node1Step5Chunk1_5_checked, root5Node1Step5Chunk2_0_checked, root5Node1Step5Chunk2_1_checked, root5Node1Step5Chunk2_2_checked, root5Node1Step5Chunk2_3_checked, root5Node1Step5Chunk2_4_checked, root5Node1Step5Chunk2_5_checked, root5Node1Step5Chunk3_0_checked, root5Node1Step5Chunk3_1_checked, root5Node1Step5Chunk3_2_checked, root5Node1Step5Chunk3_3_checked, root5Node1Step5Chunk3_4_checked, root5Node1Step5Chunk3_5_checked, root5Node1Step5Chunk4_0_checked, root5Node1Step5Chunk4_1_checked, root5Node1Step5Chunk4_2_checked, root5Node1Step5Chunk4_3_checked, root5Node1Step5Chunk4_4_checked, root5Node1Step5Chunk4_5_checked, root5Node1Step5Chunk5_0_checked, root5Node1Step5Chunk5_1_checked, root5Node1Step5Chunk5_2_checked, root5Node1Step5Chunk5_3_checked, root5Node1Step5Chunk5_4_checked, root5Node1Step5Chunk5_5_checked, root5Node1Step5Chunk6_0_checked, root5Node1Step5Chunk6_1_checked, root5Node1Step5Chunk6_2_checked, root5Node1Step5Chunk6_3_checked, root5Node1Step5Chunk6_4_checked, root5Node1Step5Chunk6_5_checked, root5Node1Step5Chunk7_0_checked, root5Node1Step5Chunk7_1_checked, root5Node1Step5Chunk7_2_checked, root5Node1Step5Chunk7_3_checked, root5Node1Step5Chunk7_4_checked, root5Node1Step5Chunk7_5_checked, root5Node1Step5Chunk8_0_checked, root5Node1Step5Chunk8_1_checked, root5Node1Step5Chunk8_2_checked, root5Node1Step5Chunk8_3_checked, root5Node1Step5Chunk8_4_checked, root5Node1Step5Chunk8_5_checked, Bool.true_and])
theorem root5Node1Step5_checked :
    checkReplacement table1 root5Node1Domains4 root5Node1Domains5 = true := by
  exact checkReplacement_of_fast_rest _ root5Node1Domains4 root5Node1Domains5
    root5Node1Domains4Fast root5Node1Domains5Fast
    root5Node1Domains4_fast_eq root5Node1Domains5_fast_eq
    root5Node1Step5Narrowing_checked (by decide)
def root5Node2Domains0 : Domains 91 State := restrict root5Node1Domains5 8 (1,1)
def root5Node2Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(4,0),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => some [(0,2),(1,0),(6,0)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(7,5),(8,1)]
  | 10 => some [(0,1),(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2),(7,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node2Domains0_fast_eq : root5Node2Domains0 = expandDomains root5Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node2Domains0 v = expandDomains root5Node2Domains0Fast v from by decide) v
def root5Node2Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(6,3),(7,3)]
  | 5 => [(2,2),(4,2)]
  | 6 => [(2,1),(2,3),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1),(5,1),(8,1)]
  | 10 => [(0,1),(0,2),(6,5)]
  | 11 => [(0,4),(1,1),(6,2)]
  | 12 => [(0,1),(1,4),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node2Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(2,3),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node2Domains1_fast_eq : root5Node2Domains1 = expandDomains root5Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node2Domains1 v = expandDomains root5Node2Domains1Fast v from by decide) v
theorem root5Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Narrowing_checked :
    checkNarrowing table10 root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_flatten table10Scope [table10Rows0_0,table10Rows0_1,table10Rows0_2,table10Rows0_3,table10Rows0_4,table10Rows0_5,table10Rows1_0,table10Rows1_1,table10Rows1_2,table10Rows1_3,table10Rows1_4,table10Rows1_5,table10Rows2_0,table10Rows2_1,table10Rows2_2,table10Rows2_3,table10Rows2_4,table10Rows2_5,table10Rows3_0,table10Rows3_1,table10Rows3_2,table10Rows3_3,table10Rows3_4,table10Rows3_5,table10Rows4_0,table10Rows4_1,table10Rows4_2,table10Rows4_3,table10Rows4_4,table10Rows4_5,table10Rows5_0,table10Rows5_1,table10Rows5_2,table10Rows5_3,table10Rows5_4,table10Rows5_5,table10Rows6_0,table10Rows6_1,table10Rows6_2,table10Rows6_3,table10Rows6_4,table10Rows6_5,table10Rows7_0,table10Rows7_1,table10Rows7_2,table10Rows7_3,table10Rows7_4,table10Rows7_5,table10Rows8_0,table10Rows8_1,table10Rows8_2,table10Rows8_3,table10Rows8_4,table10Rows8_5]
    root5Node2Domains0 root5Node2Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node2Step1Chunk0_0_checked, root5Node2Step1Chunk0_1_checked, root5Node2Step1Chunk0_2_checked, root5Node2Step1Chunk0_3_checked, root5Node2Step1Chunk0_4_checked, root5Node2Step1Chunk0_5_checked, root5Node2Step1Chunk1_0_checked, root5Node2Step1Chunk1_1_checked, root5Node2Step1Chunk1_2_checked, root5Node2Step1Chunk1_3_checked, root5Node2Step1Chunk1_4_checked, root5Node2Step1Chunk1_5_checked, root5Node2Step1Chunk2_0_checked, root5Node2Step1Chunk2_1_checked, root5Node2Step1Chunk2_2_checked, root5Node2Step1Chunk2_3_checked, root5Node2Step1Chunk2_4_checked, root5Node2Step1Chunk2_5_checked, root5Node2Step1Chunk3_0_checked, root5Node2Step1Chunk3_1_checked, root5Node2Step1Chunk3_2_checked, root5Node2Step1Chunk3_3_checked, root5Node2Step1Chunk3_4_checked, root5Node2Step1Chunk3_5_checked, root5Node2Step1Chunk4_0_checked, root5Node2Step1Chunk4_1_checked, root5Node2Step1Chunk4_2_checked, root5Node2Step1Chunk4_3_checked, root5Node2Step1Chunk4_4_checked, root5Node2Step1Chunk4_5_checked, root5Node2Step1Chunk5_0_checked, root5Node2Step1Chunk5_1_checked, root5Node2Step1Chunk5_2_checked, root5Node2Step1Chunk5_3_checked, root5Node2Step1Chunk5_4_checked, root5Node2Step1Chunk5_5_checked, root5Node2Step1Chunk6_0_checked, root5Node2Step1Chunk6_1_checked, root5Node2Step1Chunk6_2_checked, root5Node2Step1Chunk6_3_checked, root5Node2Step1Chunk6_4_checked, root5Node2Step1Chunk6_5_checked, root5Node2Step1Chunk7_0_checked, root5Node2Step1Chunk7_1_checked, root5Node2Step1Chunk7_2_checked, root5Node2Step1Chunk7_3_checked, root5Node2Step1Chunk7_4_checked, root5Node2Step1Chunk7_5_checked, root5Node2Step1Chunk8_0_checked, root5Node2Step1Chunk8_1_checked, root5Node2Step1Chunk8_2_checked, root5Node2Step1Chunk8_3_checked, root5Node2Step1Chunk8_4_checked, root5Node2Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node2Step1_checked :
    checkReplacement table10 root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq
    root5Node2Step1Narrowing_checked (by decide)
def root5Node2Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(6,3),(7,3)]
  | 5 => [(2,2),(4,2)]
  | 6 => [(2,1),(2,3),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1),(5,1),(8,1)]
  | 10 => [(0,1),(0,2),(6,5)]
  | 11 => [(0,4),(1,1),(6,2)]
  | 12 => [(0,1),(1,4),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5),(7,3)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node2Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(2,3),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node2Domains2_fast_eq : root5Node2Domains2 = expandDomains root5Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node2Domains2 v = expandDomains root5Node2Domains2Fast v from by decide) v
theorem root5Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Narrowing_checked :
    checkNarrowing table13 root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root5Node2Domains1 root5Node2Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node2Step2Chunk0_0_checked, root5Node2Step2Chunk0_1_checked, root5Node2Step2Chunk0_2_checked, root5Node2Step2Chunk0_3_checked, root5Node2Step2Chunk0_4_checked, root5Node2Step2Chunk0_5_checked, root5Node2Step2Chunk1_0_checked, root5Node2Step2Chunk1_1_checked, root5Node2Step2Chunk1_2_checked, root5Node2Step2Chunk1_3_checked, root5Node2Step2Chunk1_4_checked, root5Node2Step2Chunk1_5_checked, root5Node2Step2Chunk2_0_checked, root5Node2Step2Chunk2_1_checked, root5Node2Step2Chunk2_2_checked, root5Node2Step2Chunk2_3_checked, root5Node2Step2Chunk2_4_checked, root5Node2Step2Chunk2_5_checked, root5Node2Step2Chunk3_0_checked, root5Node2Step2Chunk3_1_checked, root5Node2Step2Chunk3_2_checked, root5Node2Step2Chunk3_3_checked, root5Node2Step2Chunk3_4_checked, root5Node2Step2Chunk3_5_checked, root5Node2Step2Chunk4_0_checked, root5Node2Step2Chunk4_1_checked, root5Node2Step2Chunk4_2_checked, root5Node2Step2Chunk4_3_checked, root5Node2Step2Chunk4_4_checked, root5Node2Step2Chunk4_5_checked, root5Node2Step2Chunk5_0_checked, root5Node2Step2Chunk5_1_checked, root5Node2Step2Chunk5_2_checked, root5Node2Step2Chunk5_3_checked, root5Node2Step2Chunk5_4_checked, root5Node2Step2Chunk5_5_checked, root5Node2Step2Chunk6_0_checked, root5Node2Step2Chunk6_1_checked, root5Node2Step2Chunk6_2_checked, root5Node2Step2Chunk6_3_checked, root5Node2Step2Chunk6_4_checked, root5Node2Step2Chunk6_5_checked, root5Node2Step2Chunk7_0_checked, root5Node2Step2Chunk7_1_checked, root5Node2Step2Chunk7_2_checked, root5Node2Step2Chunk7_3_checked, root5Node2Step2Chunk7_4_checked, root5Node2Step2Chunk7_5_checked, root5Node2Step2Chunk8_0_checked, root5Node2Step2Chunk8_1_checked, root5Node2Step2Chunk8_2_checked, root5Node2Step2Chunk8_3_checked, root5Node2Step2Chunk8_4_checked, root5Node2Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node2Step2_checked :
    checkReplacement table13 root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq
    root5Node2Step2Narrowing_checked (by decide)
def root5Node2Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(6,3),(7,3)]
  | 5 => [(2,2),(4,2)]
  | 6 => [(2,1),(2,3),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1),(5,1),(8,1)]
  | 10 => [(0,1),(0,2),(6,5)]
  | 11 => [(0,4),(1,1),(6,2)]
  | 12 => [(0,1),(1,4),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5),(7,3)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(0,3),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node2Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(6,3),(7,3)]
  | 5 => some [(2,2),(4,2)]
  | 6 => some [(2,1),(2,3),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(5,1),(8,1)]
  | 10 => some [(0,1),(0,2),(6,5)]
  | 11 => some [(0,4),(1,1),(6,2)]
  | 12 => some [(0,1),(1,4),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node2Domains3_fast_eq : root5Node2Domains3 = expandDomains root5Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node2Domains3 v = expandDomains root5Node2Domains3Fast v from by decide) v
theorem root5Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq (by decide)
theorem root5Node2Step3Narrowing_checked :
    checkNarrowing table12 root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root5Node2Domains2 root5Node2Domains3 (by
      simp only [List.all_cons, List.all_nil, root5Node2Step3Chunk0_0_checked, root5Node2Step3Chunk0_1_checked, root5Node2Step3Chunk0_2_checked, root5Node2Step3Chunk0_3_checked, root5Node2Step3Chunk0_4_checked, root5Node2Step3Chunk0_5_checked, root5Node2Step3Chunk1_0_checked, root5Node2Step3Chunk1_1_checked, root5Node2Step3Chunk1_2_checked, root5Node2Step3Chunk1_3_checked, root5Node2Step3Chunk1_4_checked, root5Node2Step3Chunk1_5_checked, root5Node2Step3Chunk2_0_checked, root5Node2Step3Chunk2_1_checked, root5Node2Step3Chunk2_2_checked, root5Node2Step3Chunk2_3_checked, root5Node2Step3Chunk2_4_checked, root5Node2Step3Chunk2_5_checked, root5Node2Step3Chunk3_0_checked, root5Node2Step3Chunk3_1_checked, root5Node2Step3Chunk3_2_checked, root5Node2Step3Chunk3_3_checked, root5Node2Step3Chunk3_4_checked, root5Node2Step3Chunk3_5_checked, root5Node2Step3Chunk4_0_checked, root5Node2Step3Chunk4_1_checked, root5Node2Step3Chunk4_2_checked, root5Node2Step3Chunk4_3_checked, root5Node2Step3Chunk4_4_checked, root5Node2Step3Chunk4_5_checked, root5Node2Step3Chunk5_0_checked, root5Node2Step3Chunk5_1_checked, root5Node2Step3Chunk5_2_checked, root5Node2Step3Chunk5_3_checked, root5Node2Step3Chunk5_4_checked, root5Node2Step3Chunk5_5_checked, root5Node2Step3Chunk6_0_checked, root5Node2Step3Chunk6_1_checked, root5Node2Step3Chunk6_2_checked, root5Node2Step3Chunk6_3_checked, root5Node2Step3Chunk6_4_checked, root5Node2Step3Chunk6_5_checked, root5Node2Step3Chunk7_0_checked, root5Node2Step3Chunk7_1_checked, root5Node2Step3Chunk7_2_checked, root5Node2Step3Chunk7_3_checked, root5Node2Step3Chunk7_4_checked, root5Node2Step3Chunk7_5_checked, root5Node2Step3Chunk8_0_checked, root5Node2Step3Chunk8_1_checked, root5Node2Step3Chunk8_2_checked, root5Node2Step3Chunk8_3_checked, root5Node2Step3Chunk8_4_checked, root5Node2Step3Chunk8_5_checked, Bool.true_and])
theorem root5Node2Step3_checked :
    checkReplacement table12 root5Node2Domains2 root5Node2Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root5Node2Domains2 root5Node2Domains3
    root5Node2Domains2Fast root5Node2Domains3Fast
    root5Node2Domains2_fast_eq root5Node2Domains3_fast_eq
    root5Node2Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
