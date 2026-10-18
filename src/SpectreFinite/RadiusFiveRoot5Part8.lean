module

public import SpectreFinite.RadiusFiveRoot5Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node16Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4),(8,4)]
  | 1 => [(0,0),(1,3),(6,3)]
  | 2 => [(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(4,1),(8,1)]
  | 7 => [(0,2),(1,5),(6,5)]
  | 8 => [(0,4),(1,1),(6,1)]
  | 9 => [(5,1),(5,4),(8,1)]
  | 10 => [(0,0),(0,1),(6,4),(6,5)]
  | 11 => [(0,4),(1,2),(6,2),(7,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(3,3),(5,3),(7,3),(8,3)]
  | 14 => [(5,2),(5,5),(8,5)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(4,3),(8,3)]
  | 17 => [(1,5),(3,5),(5,5),(7,5)]
  | 18 => [(0,3),(1,0),(3,0),(6,1)]
  | 19 => [(2,1),(2,5),(4,1)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(0,1),(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,2),(6,3)]
  | 23 => [(4,4),(7,2),(8,4)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4),(4,4)]
  | 27 => [(0,0),(1,3),(3,3),(7,3)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => [(0,2),(1,0),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(1,5),(6,5)]
  | 37 => [(0,4),(6,1),(6,2)]
  | 38 => [(5,1),(5,4),(8,4)]
  | 39 => [(0,1),(1,4),(6,4)]
  | 40 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1),(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0)]
  | 51 => [(0,3),(0,4),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(4,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2),(8,2)]
  | 72 => [(5,0),(5,3)]
  | 73 => [(4,5),(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(5,4),(7,4)]
  | 80 => [(0,0),(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(0,2),(1,5),(6,0)]
  | 87 => [(1,1),(6,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node16Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4),(8,4)]
  | 1 => some [(0,0),(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(1,5),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node16Domains4_fast_eq : root5Node16Domains4 = expandDomains root5Node16Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node16Domains4 v = expandDomains root5Node16Domains4Fast v from by decide) v
theorem root5Node16Step4Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq (by decide)
theorem root5Node16Step4Narrowing_checked :
    checkNarrowing table19 root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root5Node16Domains3 root5Node16Domains4 (by
      simp only [List.all_cons, List.all_nil, root5Node16Step4Chunk0_0_checked, root5Node16Step4Chunk0_1_checked, root5Node16Step4Chunk0_2_checked, root5Node16Step4Chunk0_3_checked, root5Node16Step4Chunk0_4_checked, root5Node16Step4Chunk0_5_checked, root5Node16Step4Chunk1_0_checked, root5Node16Step4Chunk1_1_checked, root5Node16Step4Chunk1_2_checked, root5Node16Step4Chunk1_3_checked, root5Node16Step4Chunk1_4_checked, root5Node16Step4Chunk1_5_checked, root5Node16Step4Chunk2_0_checked, root5Node16Step4Chunk2_1_checked, root5Node16Step4Chunk2_2_checked, root5Node16Step4Chunk2_3_checked, root5Node16Step4Chunk2_4_checked, root5Node16Step4Chunk2_5_checked, root5Node16Step4Chunk3_0_checked, root5Node16Step4Chunk3_1_checked, root5Node16Step4Chunk3_2_checked, root5Node16Step4Chunk3_3_checked, root5Node16Step4Chunk3_4_checked, root5Node16Step4Chunk3_5_checked, root5Node16Step4Chunk4_0_checked, root5Node16Step4Chunk4_1_checked, root5Node16Step4Chunk4_2_checked, root5Node16Step4Chunk4_3_checked, root5Node16Step4Chunk4_4_checked, root5Node16Step4Chunk4_5_checked, root5Node16Step4Chunk5_0_checked, root5Node16Step4Chunk5_1_checked, root5Node16Step4Chunk5_2_checked, root5Node16Step4Chunk5_3_checked, root5Node16Step4Chunk5_4_checked, root5Node16Step4Chunk5_5_checked, root5Node16Step4Chunk6_0_checked, root5Node16Step4Chunk6_1_checked, root5Node16Step4Chunk6_2_checked, root5Node16Step4Chunk6_3_checked, root5Node16Step4Chunk6_4_checked, root5Node16Step4Chunk6_5_checked, root5Node16Step4Chunk7_0_checked, root5Node16Step4Chunk7_1_checked, root5Node16Step4Chunk7_2_checked, root5Node16Step4Chunk7_3_checked, root5Node16Step4Chunk7_4_checked, root5Node16Step4Chunk7_5_checked, root5Node16Step4Chunk8_0_checked, root5Node16Step4Chunk8_1_checked, root5Node16Step4Chunk8_2_checked, root5Node16Step4Chunk8_3_checked, root5Node16Step4Chunk8_4_checked, root5Node16Step4Chunk8_5_checked, Bool.true_and])
theorem root5Node16Step4_checked :
    checkReplacement table19 root5Node16Domains3 root5Node16Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root5Node16Domains3 root5Node16Domains4
    root5Node16Domains3Fast root5Node16Domains4Fast
    root5Node16Domains3_fast_eq root5Node16Domains4_fast_eq
    root5Node16Step4Narrowing_checked (by decide)
def root5Node17Domains0 : Domains 91 State := restrict root5Node16Domains4 0 (7,4)
def root5Node17Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(0,0),(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(1,5),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node17Domains0_fast_eq : root5Node17Domains0 = expandDomains root5Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node17Domains0 v = expandDomains root5Node17Domains0Fast v from by decide) v
def root5Node17Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3),(6,3)]
  | 2 => [(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(4,1),(8,1)]
  | 7 => [(0,2),(6,5)]
  | 8 => [(0,4),(1,1)]
  | 9 => [(5,1),(5,4),(8,1)]
  | 10 => [(0,0),(0,1),(6,4),(6,5)]
  | 11 => [(0,4),(1,2),(6,2),(7,2)]
  | 12 => [(1,4),(7,4)]
  | 13 => [(3,3),(5,3),(7,3),(8,3)]
  | 14 => [(5,2),(5,5),(8,5)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(4,3),(8,3)]
  | 17 => [(1,5),(3,5),(5,5),(7,5)]
  | 18 => [(0,3),(1,0),(3,0),(6,1)]
  | 19 => [(2,1),(2,5),(4,1)]
  | 20 => [(0,2),(6,0)]
  | 21 => [(0,1),(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,2),(6,3)]
  | 23 => [(4,4),(7,2),(8,4)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4),(4,4)]
  | 27 => [(0,0),(1,3),(3,3),(7,3)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => [(0,2),(1,0),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(1,5),(6,5)]
  | 37 => [(0,4),(6,1),(6,2)]
  | 38 => [(5,1),(5,4),(8,4)]
  | 39 => [(0,1),(1,4),(6,4)]
  | 40 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1),(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0)]
  | 51 => [(0,3),(0,4),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(4,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2),(8,2)]
  | 72 => [(5,0),(5,3)]
  | 73 => [(4,5),(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(5,4),(7,4)]
  | 80 => [(0,0),(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(0,2),(1,5),(6,0)]
  | 87 => [(1,1),(6,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node17Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(6,5)]
  | 8 => some [(0,4),(1,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node17Domains1_fast_eq : root5Node17Domains1 = expandDomains root5Node17Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node17Domains1 v = expandDomains root5Node17Domains1Fast v from by decide) v
theorem root5Node17Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq (by decide)
theorem root5Node17Step1Narrowing_checked :
    checkNarrowing table0 root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root5Node17Domains0 root5Node17Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node17Step1Chunk0_0_checked, root5Node17Step1Chunk0_1_checked, root5Node17Step1Chunk0_2_checked, root5Node17Step1Chunk0_3_checked, root5Node17Step1Chunk0_4_checked, root5Node17Step1Chunk0_5_checked, root5Node17Step1Chunk1_0_checked, root5Node17Step1Chunk1_1_checked, root5Node17Step1Chunk1_2_checked, root5Node17Step1Chunk1_3_checked, root5Node17Step1Chunk1_4_checked, root5Node17Step1Chunk1_5_checked, root5Node17Step1Chunk2_0_checked, root5Node17Step1Chunk2_1_checked, root5Node17Step1Chunk2_2_checked, root5Node17Step1Chunk2_3_checked, root5Node17Step1Chunk2_4_checked, root5Node17Step1Chunk2_5_checked, root5Node17Step1Chunk3_0_checked, root5Node17Step1Chunk3_1_checked, root5Node17Step1Chunk3_2_checked, root5Node17Step1Chunk3_3_checked, root5Node17Step1Chunk3_4_checked, root5Node17Step1Chunk3_5_checked, root5Node17Step1Chunk4_0_checked, root5Node17Step1Chunk4_1_checked, root5Node17Step1Chunk4_2_checked, root5Node17Step1Chunk4_3_checked, root5Node17Step1Chunk4_4_checked, root5Node17Step1Chunk4_5_checked, root5Node17Step1Chunk5_0_checked, root5Node17Step1Chunk5_1_checked, root5Node17Step1Chunk5_2_checked, root5Node17Step1Chunk5_3_checked, root5Node17Step1Chunk5_4_checked, root5Node17Step1Chunk5_5_checked, root5Node17Step1Chunk6_0_checked, root5Node17Step1Chunk6_1_checked, root5Node17Step1Chunk6_2_checked, root5Node17Step1Chunk6_3_checked, root5Node17Step1Chunk6_4_checked, root5Node17Step1Chunk6_5_checked, root5Node17Step1Chunk7_0_checked, root5Node17Step1Chunk7_1_checked, root5Node17Step1Chunk7_2_checked, root5Node17Step1Chunk7_3_checked, root5Node17Step1Chunk7_4_checked, root5Node17Step1Chunk7_5_checked, root5Node17Step1Chunk8_0_checked, root5Node17Step1Chunk8_1_checked, root5Node17Step1Chunk8_2_checked, root5Node17Step1Chunk8_3_checked, root5Node17Step1Chunk8_4_checked, root5Node17Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node17Step1_checked :
    checkReplacement table0 root5Node17Domains0 root5Node17Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node17Domains0 root5Node17Domains1
    root5Node17Domains0Fast root5Node17Domains1Fast
    root5Node17Domains0_fast_eq root5Node17Domains1_fast_eq
    root5Node17Step1Narrowing_checked (by decide)
def root5Node18Domains0 : Domains 91 State := restrict root5Node17Domains1 1 (1,3)
def root5Node18Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(4,1),(8,1)]
  | 7 => some [(0,2),(6,5)]
  | 8 => some [(0,4),(1,1)]
  | 9 => some [(5,1),(5,4),(8,1)]
  | 10 => some [(0,0),(0,1),(6,4),(6,5)]
  | 11 => some [(0,4),(1,2),(6,2),(7,2)]
  | 12 => some [(1,4),(7,4)]
  | 13 => some [(3,3),(5,3),(7,3),(8,3)]
  | 14 => some [(5,2),(5,5),(8,5)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(4,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,5),(7,5)]
  | 18 => some [(0,3),(1,0),(3,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1)]
  | 20 => some [(0,2),(6,0)]
  | 21 => some [(0,1),(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,2),(6,3)]
  | 23 => some [(4,4),(7,2),(8,4)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node18Domains0_fast_eq : root5Node18Domains0 = expandDomains root5Node18Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node18Domains0 v = expandDomains root5Node18Domains0Fast v from by decide) v
def root5Node18Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0),(8,0)]
  | 4 => [(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(0,0),(6,4)]
  | 11 => [(1,2),(7,2)]
  | 12 => [(7,4)]
  | 13 => [(5,3),(8,3)]
  | 14 => [(5,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(1,5),(3,5),(7,5)]
  | 18 => [(0,3),(6,1)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,3)]
  | 23 => [(4,4),(7,2)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4)]
  | 27 => [(1,3),(3,3),(7,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => [(0,2),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(0,1),(1,4),(6,4)]
  | 40 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0)]
  | 51 => [(0,3),(0,4),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(4,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2),(8,2)]
  | 72 => [(5,0),(5,3)]
  | 73 => [(4,5),(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(5,4),(7,4)]
  | 80 => [(0,0),(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(0,2),(1,5),(6,0)]
  | 87 => [(1,1),(6,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node18Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0),(8,0)]
  | 4 => some [(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0),(6,4)]
  | 11 => some [(1,2),(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(5,3),(8,3)]
  | 14 => some [(5,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5),(3,5),(7,5)]
  | 18 => some [(0,3),(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,3)]
  | 23 => some [(4,4),(7,2)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4)]
  | 27 => some [(1,3),(3,3),(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node18Domains1_fast_eq : root5Node18Domains1 = expandDomains root5Node18Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node18Domains1 v = expandDomains root5Node18Domains1Fast v from by decide) v
theorem root5Node18Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq (by decide)
theorem root5Node18Step1Narrowing_checked :
    checkNarrowing table25 root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root5Node18Domains0 root5Node18Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node18Step1Chunk0_0_checked, root5Node18Step1Chunk0_1_checked, root5Node18Step1Chunk0_2_checked, root5Node18Step1Chunk0_3_checked, root5Node18Step1Chunk0_4_checked, root5Node18Step1Chunk0_5_checked, root5Node18Step1Chunk1_0_checked, root5Node18Step1Chunk1_1_checked, root5Node18Step1Chunk1_2_checked, root5Node18Step1Chunk1_3_checked, root5Node18Step1Chunk1_4_checked, root5Node18Step1Chunk1_5_checked, root5Node18Step1Chunk2_0_checked, root5Node18Step1Chunk2_1_checked, root5Node18Step1Chunk2_2_checked, root5Node18Step1Chunk2_3_checked, root5Node18Step1Chunk2_4_checked, root5Node18Step1Chunk2_5_checked, root5Node18Step1Chunk3_0_checked, root5Node18Step1Chunk3_1_checked, root5Node18Step1Chunk3_2_checked, root5Node18Step1Chunk3_3_checked, root5Node18Step1Chunk3_4_checked, root5Node18Step1Chunk3_5_checked, root5Node18Step1Chunk4_0_checked, root5Node18Step1Chunk4_1_checked, root5Node18Step1Chunk4_2_checked, root5Node18Step1Chunk4_3_checked, root5Node18Step1Chunk4_4_checked, root5Node18Step1Chunk4_5_checked, root5Node18Step1Chunk5_0_checked, root5Node18Step1Chunk5_1_checked, root5Node18Step1Chunk5_2_checked, root5Node18Step1Chunk5_3_checked, root5Node18Step1Chunk5_4_checked, root5Node18Step1Chunk5_5_checked, root5Node18Step1Chunk6_0_checked, root5Node18Step1Chunk6_1_checked, root5Node18Step1Chunk6_2_checked, root5Node18Step1Chunk6_3_checked, root5Node18Step1Chunk6_4_checked, root5Node18Step1Chunk6_5_checked, root5Node18Step1Chunk7_0_checked, root5Node18Step1Chunk7_1_checked, root5Node18Step1Chunk7_2_checked, root5Node18Step1Chunk7_3_checked, root5Node18Step1Chunk7_4_checked, root5Node18Step1Chunk7_5_checked, root5Node18Step1Chunk8_0_checked, root5Node18Step1Chunk8_1_checked, root5Node18Step1Chunk8_2_checked, root5Node18Step1Chunk8_3_checked, root5Node18Step1Chunk8_4_checked, root5Node18Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node18Step1_checked :
    checkReplacement table25 root5Node18Domains0 root5Node18Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node18Domains0 root5Node18Domains1
    root5Node18Domains0Fast root5Node18Domains1Fast
    root5Node18Domains0_fast_eq root5Node18Domains1_fast_eq
    root5Node18Step1Narrowing_checked (by decide)
def root5Node18Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0),(8,0)]
  | 4 => [(4,5),(7,3)]
  | 5 => [(4,2),(7,0)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(0,0),(6,4)]
  | 11 => [(1,2),(7,2)]
  | 12 => [(7,4)]
  | 13 => [(5,3),(8,3)]
  | 14 => [(5,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(1,5),(3,5),(7,5)]
  | 18 => [(0,3),(6,1)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4),(3,4),(7,4)]
  | 22 => [(0,5),(6,3)]
  | 23 => [(4,4),(7,2)]
  | 24 => [(1,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(2,0),(2,2),(2,4)]
  | 27 => [(1,3),(3,3),(7,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => [(0,2),(6,0)]
  | 32 => [(1,1),(7,1)]
  | 33 => [(4,1),(7,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(3,1),(7,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => [(4,0),(8,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2),(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(1,0),(7,0)]
  | 48 => [(4,3),(7,1)]
  | 49 => [(7,5)]
  | 50 => [(0,3),(6,0)]
  | 51 => [(0,3),(0,4),(6,1),(6,2)]
  | 52 => [(5,1),(5,4),(8,4)]
  | 53 => [(0,1),(6,4)]
  | 54 => [(1,2),(6,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(4,0),(7,4)]
  | 59 => [(1,3),(7,3)]
  | 60 => [(4,2),(8,2)]
  | 61 => [(4,3),(5,3),(7,1),(8,3)]
  | 62 => [(7,5),(8,5)]
  | 63 => [(0,3),(1,0)]
  | 64 => [(7,1),(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(5,1),(8,1)]
  | 68 => [(0,1),(6,5)]
  | 69 => [(0,4),(6,2)]
  | 70 => [(1,3),(7,3)]
  | 71 => [(4,2),(8,2)]
  | 72 => [(5,0),(5,3)]
  | 73 => [(4,5),(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(1,0),(3,0),(7,0)]
  | 78 => [(0,4),(1,2),(6,2)]
  | 79 => [(1,4),(3,4),(5,4),(7,4)]
  | 80 => [(0,0),(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(1,3),(6,3)]
  | 84 => [(4,4),(7,2),(8,2)]
  | 85 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => [(0,2),(1,5),(6,0)]
  | 87 => [(1,1),(6,1),(7,1)]
  | 88 => [(4,1),(7,5),(8,1)]
  | 89 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node18Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0),(8,0)]
  | 4 => some [(4,5),(7,3)]
  | 5 => some [(4,2),(7,0)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(0,0),(6,4)]
  | 11 => some [(1,2),(7,2)]
  | 12 => some [(7,4)]
  | 13 => some [(5,3),(8,3)]
  | 14 => some [(5,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(1,5),(3,5),(7,5)]
  | 18 => some [(0,3),(6,1)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4),(3,4),(7,4)]
  | 22 => some [(0,5),(6,3)]
  | 23 => some [(4,4),(7,2)]
  | 24 => some [(1,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4)]
  | 27 => some [(1,3),(3,3),(7,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 31 => some [(0,2),(6,0)]
  | 32 => some [(1,1),(7,1)]
  | 33 => some [(4,1),(7,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(0,3),(6,0)]
  | 51 => some [(0,3),(0,4),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,4)]
  | 53 => some [(0,1),(6,4)]
  | 54 => some [(1,2),(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(7,3)]
  | 60 => some [(4,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(7,5),(8,5)]
  | 63 => some [(0,3),(1,0)]
  | 64 => some [(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(5,1),(8,1)]
  | 68 => some [(0,1),(6,5)]
  | 69 => some [(0,4),(6,2)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2),(8,2)]
  | 72 => some [(5,0),(5,3)]
  | 73 => some [(4,5),(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0)]
  | 78 => some [(0,4),(1,2),(6,2)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4)]
  | 80 => some [(0,0),(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 86 => some [(0,2),(1,5),(6,0)]
  | 87 => some [(1,1),(6,1),(7,1)]
  | 88 => some [(4,1),(7,5),(8,1)]
  | 89 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node18Domains2_fast_eq : root5Node18Domains2 = expandDomains root5Node18Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node18Domains2 v = expandDomains root5Node18Domains2Fast v from by decide) v
theorem root5Node18Step2Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq (by decide)
theorem root5Node18Step2Narrowing_checked :
    checkNarrowing table12 root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root5Node18Domains1 root5Node18Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node18Step2Chunk0_0_checked, root5Node18Step2Chunk0_1_checked, root5Node18Step2Chunk0_2_checked, root5Node18Step2Chunk0_3_checked, root5Node18Step2Chunk0_4_checked, root5Node18Step2Chunk0_5_checked, root5Node18Step2Chunk1_0_checked, root5Node18Step2Chunk1_1_checked, root5Node18Step2Chunk1_2_checked, root5Node18Step2Chunk1_3_checked, root5Node18Step2Chunk1_4_checked, root5Node18Step2Chunk1_5_checked, root5Node18Step2Chunk2_0_checked, root5Node18Step2Chunk2_1_checked, root5Node18Step2Chunk2_2_checked, root5Node18Step2Chunk2_3_checked, root5Node18Step2Chunk2_4_checked, root5Node18Step2Chunk2_5_checked, root5Node18Step2Chunk3_0_checked, root5Node18Step2Chunk3_1_checked, root5Node18Step2Chunk3_2_checked, root5Node18Step2Chunk3_3_checked, root5Node18Step2Chunk3_4_checked, root5Node18Step2Chunk3_5_checked, root5Node18Step2Chunk4_0_checked, root5Node18Step2Chunk4_1_checked, root5Node18Step2Chunk4_2_checked, root5Node18Step2Chunk4_3_checked, root5Node18Step2Chunk4_4_checked, root5Node18Step2Chunk4_5_checked, root5Node18Step2Chunk5_0_checked, root5Node18Step2Chunk5_1_checked, root5Node18Step2Chunk5_2_checked, root5Node18Step2Chunk5_3_checked, root5Node18Step2Chunk5_4_checked, root5Node18Step2Chunk5_5_checked, root5Node18Step2Chunk6_0_checked, root5Node18Step2Chunk6_1_checked, root5Node18Step2Chunk6_2_checked, root5Node18Step2Chunk6_3_checked, root5Node18Step2Chunk6_4_checked, root5Node18Step2Chunk6_5_checked, root5Node18Step2Chunk7_0_checked, root5Node18Step2Chunk7_1_checked, root5Node18Step2Chunk7_2_checked, root5Node18Step2Chunk7_3_checked, root5Node18Step2Chunk7_4_checked, root5Node18Step2Chunk7_5_checked, root5Node18Step2Chunk8_0_checked, root5Node18Step2Chunk8_1_checked, root5Node18Step2Chunk8_2_checked, root5Node18Step2Chunk8_3_checked, root5Node18Step2Chunk8_4_checked, root5Node18Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node18Step2_checked :
    checkReplacement table12 root5Node18Domains1 root5Node18Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node18Domains1 root5Node18Domains2
    root5Node18Domains1Fast root5Node18Domains2Fast
    root5Node18Domains1_fast_eq root5Node18Domains2_fast_eq
    root5Node18Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
