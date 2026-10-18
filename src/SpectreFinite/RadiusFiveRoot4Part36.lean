module

public import SpectreFinite.RadiusFiveRoot4Part35
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable51

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node88Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,1),(2,3)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(0,0),(6,4)]
  | 14 => [(1,2),(3,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(1,5),(7,5)]
  | 22 => [(0,3),(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(4,5),(7,3)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(5,3),(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(0,0),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3),(6,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(1,3),(3,3),(7,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,4),(6,2)]
  | 71 => [(5,4),(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(4,3),(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(1,3),(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node88Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(0,0),(6,4)]
  | 14 => some [(1,2),(3,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(1,5),(7,5)]
  | 22 => some [(0,3),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(5,3),(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(1,3),(3,3),(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3),(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3),(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node88Domains4_fast_eq : root4Node88Domains4 = expandDomains root4Node88Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node88Domains4 v = expandDomains root4Node88Domains4Fast v from by decide) v
theorem root4Node88Step4Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq (by decide)
theorem root4Node88Step4Narrowing_checked :
    checkNarrowing table19 root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root4Node88Domains3 root4Node88Domains4 (by
      simp only [List.all_cons, List.all_nil, root4Node88Step4Chunk0_0_checked, root4Node88Step4Chunk0_1_checked, root4Node88Step4Chunk0_2_checked, root4Node88Step4Chunk0_3_checked, root4Node88Step4Chunk0_4_checked, root4Node88Step4Chunk0_5_checked, root4Node88Step4Chunk1_0_checked, root4Node88Step4Chunk1_1_checked, root4Node88Step4Chunk1_2_checked, root4Node88Step4Chunk1_3_checked, root4Node88Step4Chunk1_4_checked, root4Node88Step4Chunk1_5_checked, root4Node88Step4Chunk2_0_checked, root4Node88Step4Chunk2_1_checked, root4Node88Step4Chunk2_2_checked, root4Node88Step4Chunk2_3_checked, root4Node88Step4Chunk2_4_checked, root4Node88Step4Chunk2_5_checked, root4Node88Step4Chunk3_0_checked, root4Node88Step4Chunk3_1_checked, root4Node88Step4Chunk3_2_checked, root4Node88Step4Chunk3_3_checked, root4Node88Step4Chunk3_4_checked, root4Node88Step4Chunk3_5_checked, root4Node88Step4Chunk4_0_checked, root4Node88Step4Chunk4_1_checked, root4Node88Step4Chunk4_2_checked, root4Node88Step4Chunk4_3_checked, root4Node88Step4Chunk4_4_checked, root4Node88Step4Chunk4_5_checked, root4Node88Step4Chunk5_0_checked, root4Node88Step4Chunk5_1_checked, root4Node88Step4Chunk5_2_checked, root4Node88Step4Chunk5_3_checked, root4Node88Step4Chunk5_4_checked, root4Node88Step4Chunk5_5_checked, root4Node88Step4Chunk6_0_checked, root4Node88Step4Chunk6_1_checked, root4Node88Step4Chunk6_2_checked, root4Node88Step4Chunk6_3_checked, root4Node88Step4Chunk6_4_checked, root4Node88Step4Chunk6_5_checked, root4Node88Step4Chunk7_0_checked, root4Node88Step4Chunk7_1_checked, root4Node88Step4Chunk7_2_checked, root4Node88Step4Chunk7_3_checked, root4Node88Step4Chunk7_4_checked, root4Node88Step4Chunk7_5_checked, root4Node88Step4Chunk8_0_checked, root4Node88Step4Chunk8_1_checked, root4Node88Step4Chunk8_2_checked, root4Node88Step4Chunk8_3_checked, root4Node88Step4Chunk8_4_checked, root4Node88Step4Chunk8_5_checked, Bool.true_and])
theorem root4Node88Step4_checked :
    checkReplacement table19 root4Node88Domains3 root4Node88Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root4Node88Domains3 root4Node88Domains4
    root4Node88Domains3Fast root4Node88Domains4Fast
    root4Node88Domains3_fast_eq root4Node88Domains4_fast_eq
    root4Node88Step4Narrowing_checked (by decide)
def root4Node89Domains0 : Domains 91 State := restrict root4Node88Domains4 0 (3,4)
def root4Node89Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,1),(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(0,0),(6,4)]
  | 14 => some [(1,2),(3,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(1,5),(7,5)]
  | 22 => some [(0,3),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(5,3),(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(1,3),(3,3),(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3),(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3),(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node89Domains0_fast_eq : root4Node89Domains0 = expandDomains root4Node89Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node89Domains0 v = expandDomains root4Node89Domains0Fast v from by decide) v
def root4Node89Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,3)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(1,3),(3,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,4),(6,2)]
  | 71 => [(5,4),(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(4,3),(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(1,3),(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node89Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(1,3),(3,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3),(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3),(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node89Domains1_fast_eq : root4Node89Domains1 = expandDomains root4Node89Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node89Domains1 v = expandDomains root4Node89Domains1Fast v from by decide) v
theorem root4Node89Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq (by decide)
theorem root4Node89Step1Narrowing_checked :
    checkNarrowing table21 root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root4Node89Domains0 root4Node89Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node89Step1Chunk0_0_checked, root4Node89Step1Chunk0_1_checked, root4Node89Step1Chunk0_2_checked, root4Node89Step1Chunk0_3_checked, root4Node89Step1Chunk0_4_checked, root4Node89Step1Chunk0_5_checked, root4Node89Step1Chunk1_0_checked, root4Node89Step1Chunk1_1_checked, root4Node89Step1Chunk1_2_checked, root4Node89Step1Chunk1_3_checked, root4Node89Step1Chunk1_4_checked, root4Node89Step1Chunk1_5_checked, root4Node89Step1Chunk2_0_checked, root4Node89Step1Chunk2_1_checked, root4Node89Step1Chunk2_2_checked, root4Node89Step1Chunk2_3_checked, root4Node89Step1Chunk2_4_checked, root4Node89Step1Chunk2_5_checked, root4Node89Step1Chunk3_0_checked, root4Node89Step1Chunk3_1_checked, root4Node89Step1Chunk3_2_checked, root4Node89Step1Chunk3_3_checked, root4Node89Step1Chunk3_4_checked, root4Node89Step1Chunk3_5_checked, root4Node89Step1Chunk4_0_checked, root4Node89Step1Chunk4_1_checked, root4Node89Step1Chunk4_2_checked, root4Node89Step1Chunk4_3_checked, root4Node89Step1Chunk4_4_checked, root4Node89Step1Chunk4_5_checked, root4Node89Step1Chunk5_0_checked, root4Node89Step1Chunk5_1_checked, root4Node89Step1Chunk5_2_checked, root4Node89Step1Chunk5_3_checked, root4Node89Step1Chunk5_4_checked, root4Node89Step1Chunk5_5_checked, root4Node89Step1Chunk6_0_checked, root4Node89Step1Chunk6_1_checked, root4Node89Step1Chunk6_2_checked, root4Node89Step1Chunk6_3_checked, root4Node89Step1Chunk6_4_checked, root4Node89Step1Chunk6_5_checked, root4Node89Step1Chunk7_0_checked, root4Node89Step1Chunk7_1_checked, root4Node89Step1Chunk7_2_checked, root4Node89Step1Chunk7_3_checked, root4Node89Step1Chunk7_4_checked, root4Node89Step1Chunk7_5_checked, root4Node89Step1Chunk8_0_checked, root4Node89Step1Chunk8_1_checked, root4Node89Step1Chunk8_2_checked, root4Node89Step1Chunk8_3_checked, root4Node89Step1Chunk8_4_checked, root4Node89Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node89Step1_checked :
    checkReplacement table21 root4Node89Domains0 root4Node89Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node89Domains0 root4Node89Domains1
    root4Node89Domains0Fast root4Node89Domains1Fast
    root4Node89Domains0_fast_eq root4Node89Domains1_fast_eq
    root4Node89Step1Narrowing_checked (by decide)
def root4Node90Domains0 : Domains 91 State := restrict root4Node89Domains1 61 (1,3)
def root4Node90Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(1,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3),(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3),(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node90Domains0_fast_eq : root4Node90Domains0 = expandDomains root4Node90Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node90Domains0 v = expandDomains root4Node90Domains0Fast v from by decide) v
def root4Node90Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,3)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(1,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(4,3)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(1,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node90Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(1,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node90Domains1_fast_eq : root4Node90Domains1 = expandDomains root4Node90Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node90Domains1 v = expandDomains root4Node90Domains1Fast v from by decide) v
theorem root4Node90Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq (by decide)
theorem root4Node90Step1Narrowing_checked :
    checkNarrowing table51 root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root4Node90Domains0 root4Node90Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node90Step1Chunk0_0_checked, root4Node90Step1Chunk0_1_checked, root4Node90Step1Chunk0_2_checked, root4Node90Step1Chunk0_3_checked, root4Node90Step1Chunk0_4_checked, root4Node90Step1Chunk0_5_checked, root4Node90Step1Chunk1_0_checked, root4Node90Step1Chunk1_1_checked, root4Node90Step1Chunk1_2_checked, root4Node90Step1Chunk1_3_checked, root4Node90Step1Chunk1_4_checked, root4Node90Step1Chunk1_5_checked, root4Node90Step1Chunk2_0_checked, root4Node90Step1Chunk2_1_checked, root4Node90Step1Chunk2_2_checked, root4Node90Step1Chunk2_3_checked, root4Node90Step1Chunk2_4_checked, root4Node90Step1Chunk2_5_checked, root4Node90Step1Chunk3_0_checked, root4Node90Step1Chunk3_1_checked, root4Node90Step1Chunk3_2_checked, root4Node90Step1Chunk3_3_checked, root4Node90Step1Chunk3_4_checked, root4Node90Step1Chunk3_5_checked, root4Node90Step1Chunk4_0_checked, root4Node90Step1Chunk4_1_checked, root4Node90Step1Chunk4_2_checked, root4Node90Step1Chunk4_3_checked, root4Node90Step1Chunk4_4_checked, root4Node90Step1Chunk4_5_checked, root4Node90Step1Chunk5_0_checked, root4Node90Step1Chunk5_1_checked, root4Node90Step1Chunk5_2_checked, root4Node90Step1Chunk5_3_checked, root4Node90Step1Chunk5_4_checked, root4Node90Step1Chunk5_5_checked, root4Node90Step1Chunk6_0_checked, root4Node90Step1Chunk6_1_checked, root4Node90Step1Chunk6_2_checked, root4Node90Step1Chunk6_3_checked, root4Node90Step1Chunk6_4_checked, root4Node90Step1Chunk6_5_checked, root4Node90Step1Chunk7_0_checked, root4Node90Step1Chunk7_1_checked, root4Node90Step1Chunk7_2_checked, root4Node90Step1Chunk7_3_checked, root4Node90Step1Chunk7_4_checked, root4Node90Step1Chunk7_5_checked, root4Node90Step1Chunk8_0_checked, root4Node90Step1Chunk8_1_checked, root4Node90Step1Chunk8_2_checked, root4Node90Step1Chunk8_3_checked, root4Node90Step1Chunk8_4_checked, root4Node90Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node90Step1_checked :
    checkReplacement table51 root4Node90Domains0 root4Node90Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node90Domains0 root4Node90Domains1
    root4Node90Domains0Fast root4Node90Domains1Fast
    root4Node90Domains0_fast_eq root4Node90Domains1_fast_eq
    root4Node90Step1Narrowing_checked (by decide)
theorem root4Node90Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node90Domains1 (.output 44) = true := by decide
def root4Node91Domains0 : Domains 91 State := restrict root4Node89Domains1 61 (3,3)
def root4Node91Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(3,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3),(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3),(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node91Domains0_fast_eq : root4Node91Domains0 = expandDomains root4Node91Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node91Domains0 v = expandDomains root4Node91Domains0Fast v from by decide) v
def root4Node91Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(7,2)]
  | 6 => [(2,3)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1)]
  | 10 => [(0,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(6,4)]
  | 14 => [(1,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(7,5)]
  | 22 => [(0,3)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(7,3)]
  | 31 => [(4,2)]
  | 32 => [(5,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(0,3)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(3,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0)]
  | 76 => [(3,2)]
  | 77 => [(4,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node91Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(7,2)]
  | 6 => some [(2,3)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1)]
  | 10 => some [(0,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(6,4)]
  | 14 => some [(1,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(7,5)]
  | 22 => some [(0,3)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(7,3)]
  | 31 => some [(4,2)]
  | 32 => some [(5,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(0,3)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(3,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0)]
  | 76 => some [(3,2)]
  | 77 => some [(4,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node91Domains1_fast_eq : root4Node91Domains1 = expandDomains root4Node91Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node91Domains1 v = expandDomains root4Node91Domains1Fast v from by decide) v
theorem root4Node91Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq (by decide)
theorem root4Node91Step1Narrowing_checked :
    checkNarrowing table51 root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root4Node91Domains0 root4Node91Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node91Step1Chunk0_0_checked, root4Node91Step1Chunk0_1_checked, root4Node91Step1Chunk0_2_checked, root4Node91Step1Chunk0_3_checked, root4Node91Step1Chunk0_4_checked, root4Node91Step1Chunk0_5_checked, root4Node91Step1Chunk1_0_checked, root4Node91Step1Chunk1_1_checked, root4Node91Step1Chunk1_2_checked, root4Node91Step1Chunk1_3_checked, root4Node91Step1Chunk1_4_checked, root4Node91Step1Chunk1_5_checked, root4Node91Step1Chunk2_0_checked, root4Node91Step1Chunk2_1_checked, root4Node91Step1Chunk2_2_checked, root4Node91Step1Chunk2_3_checked, root4Node91Step1Chunk2_4_checked, root4Node91Step1Chunk2_5_checked, root4Node91Step1Chunk3_0_checked, root4Node91Step1Chunk3_1_checked, root4Node91Step1Chunk3_2_checked, root4Node91Step1Chunk3_3_checked, root4Node91Step1Chunk3_4_checked, root4Node91Step1Chunk3_5_checked, root4Node91Step1Chunk4_0_checked, root4Node91Step1Chunk4_1_checked, root4Node91Step1Chunk4_2_checked, root4Node91Step1Chunk4_3_checked, root4Node91Step1Chunk4_4_checked, root4Node91Step1Chunk4_5_checked, root4Node91Step1Chunk5_0_checked, root4Node91Step1Chunk5_1_checked, root4Node91Step1Chunk5_2_checked, root4Node91Step1Chunk5_3_checked, root4Node91Step1Chunk5_4_checked, root4Node91Step1Chunk5_5_checked, root4Node91Step1Chunk6_0_checked, root4Node91Step1Chunk6_1_checked, root4Node91Step1Chunk6_2_checked, root4Node91Step1Chunk6_3_checked, root4Node91Step1Chunk6_4_checked, root4Node91Step1Chunk6_5_checked, root4Node91Step1Chunk7_0_checked, root4Node91Step1Chunk7_1_checked, root4Node91Step1Chunk7_2_checked, root4Node91Step1Chunk7_3_checked, root4Node91Step1Chunk7_4_checked, root4Node91Step1Chunk7_5_checked, root4Node91Step1Chunk8_0_checked, root4Node91Step1Chunk8_1_checked, root4Node91Step1Chunk8_2_checked, root4Node91Step1Chunk8_3_checked, root4Node91Step1Chunk8_4_checked, root4Node91Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node91Step1_checked :
    checkReplacement table51 root4Node91Domains0 root4Node91Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node91Domains0 root4Node91Domains1
    root4Node91Domains0Fast root4Node91Domains1Fast
    root4Node91Domains0_fast_eq root4Node91Domains1_fast_eq
    root4Node91Step1Narrowing_checked (by decide)
theorem root4Node91Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node91Domains1 (.output 45) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
