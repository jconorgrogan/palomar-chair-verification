module

public import SpectreFinite.RadiusFiveRoot7Part51
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable32
public import SpectreFinite.RadiusFiveTable53

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node129Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(3,2),(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2),(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5),(7,5)]
  | 8 => [(0,3),(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0),(5,3),(8,0)]
  | 14 => [(4,5),(7,3),(8,5)]
  | 15 => [(4,2),(7,0)]
  | 16 => [(5,3),(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(5,4),(7,4),(8,4)]
  | 22 => [(0,0),(6,3),(6,4)]
  | 23 => [(1,2),(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(4,1),(4,3),(7,1),(8,1)]
  | 31 => [(0,2),(1,5),(7,5)]
  | 32 => [(0,3),(1,1),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 41 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(7,0),(8,0)]
  | 43 => [(5,3),(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5)]
  | 51 => [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(3,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,3),(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4),(6,4)]
  | 81 => [(0,5),(1,2),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(5,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node129Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(8,4)]
  | 1 => some [(0,0),(6,4)]
  | 2 => some [(1,2),(3,2),(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(7,3),(8,5)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(6,3),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node129Domains4_fast_eq : root7Node129Domains4 = expandDomains root7Node129Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node129Domains4 v = expandDomains root7Node129Domains4Fast v from by decide) v
theorem root7Node129Step4Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq (by decide)
theorem root7Node129Step4Narrowing_checked :
    checkNarrowing table12 root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root7Node129Domains3 root7Node129Domains4 (by
      simp only [List.all_cons, List.all_nil, root7Node129Step4Chunk0_0_checked, root7Node129Step4Chunk0_1_checked, root7Node129Step4Chunk0_2_checked, root7Node129Step4Chunk0_3_checked, root7Node129Step4Chunk0_4_checked, root7Node129Step4Chunk0_5_checked, root7Node129Step4Chunk1_0_checked, root7Node129Step4Chunk1_1_checked, root7Node129Step4Chunk1_2_checked, root7Node129Step4Chunk1_3_checked, root7Node129Step4Chunk1_4_checked, root7Node129Step4Chunk1_5_checked, root7Node129Step4Chunk2_0_checked, root7Node129Step4Chunk2_1_checked, root7Node129Step4Chunk2_2_checked, root7Node129Step4Chunk2_3_checked, root7Node129Step4Chunk2_4_checked, root7Node129Step4Chunk2_5_checked, root7Node129Step4Chunk3_0_checked, root7Node129Step4Chunk3_1_checked, root7Node129Step4Chunk3_2_checked, root7Node129Step4Chunk3_3_checked, root7Node129Step4Chunk3_4_checked, root7Node129Step4Chunk3_5_checked, root7Node129Step4Chunk4_0_checked, root7Node129Step4Chunk4_1_checked, root7Node129Step4Chunk4_2_checked, root7Node129Step4Chunk4_3_checked, root7Node129Step4Chunk4_4_checked, root7Node129Step4Chunk4_5_checked, root7Node129Step4Chunk5_0_checked, root7Node129Step4Chunk5_1_checked, root7Node129Step4Chunk5_2_checked, root7Node129Step4Chunk5_3_checked, root7Node129Step4Chunk5_4_checked, root7Node129Step4Chunk5_5_checked, root7Node129Step4Chunk6_0_checked, root7Node129Step4Chunk6_1_checked, root7Node129Step4Chunk6_2_checked, root7Node129Step4Chunk6_3_checked, root7Node129Step4Chunk6_4_checked, root7Node129Step4Chunk6_5_checked, root7Node129Step4Chunk7_0_checked, root7Node129Step4Chunk7_1_checked, root7Node129Step4Chunk7_2_checked, root7Node129Step4Chunk7_3_checked, root7Node129Step4Chunk7_4_checked, root7Node129Step4Chunk7_5_checked, root7Node129Step4Chunk8_0_checked, root7Node129Step4Chunk8_1_checked, root7Node129Step4Chunk8_2_checked, root7Node129Step4Chunk8_3_checked, root7Node129Step4Chunk8_4_checked, root7Node129Step4Chunk8_5_checked, Bool.true_and])
theorem root7Node129Step4_checked :
    checkReplacement table12 root7Node129Domains3 root7Node129Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root7Node129Domains3 root7Node129Domains4
    root7Node129Domains3Fast root7Node129Domains4Fast
    root7Node129Domains3_fast_eq root7Node129Domains4_fast_eq
    root7Node129Step4Narrowing_checked (by decide)
def root7Node130Domains0 : Domains 91 State := restrict root7Node129Domains4 0 (4,4)
def root7Node130Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(0,0),(6,4)]
  | 2 => some [(1,2),(3,2),(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(7,3),(8,5)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(6,3),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node130Domains0_fast_eq : root7Node130Domains0 = expandDomains root7Node130Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node130Domains0 v = expandDomains root7Node130Domains0Fast v from by decide) v
def root7Node130Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(3,2),(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(1,5),(7,5)]
  | 8 => [(0,3),(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0),(8,0)]
  | 14 => [(4,5),(7,3)]
  | 15 => [(4,2),(7,0)]
  | 16 => [(5,3),(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(5,4),(8,4)]
  | 22 => [(0,0),(6,4)]
  | 23 => [(1,2),(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(4,3),(7,1),(8,1)]
  | 31 => [(1,5),(7,5)]
  | 32 => [(0,3),(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 41 => [(1,3),(4,5),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(7,0)]
  | 43 => [(5,3),(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5)]
  | 51 => [(0,0),(0,1),(0,5),(6,3),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(4,4),(6,2),(7,2)]
  | 53 => [(1,4),(3,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(3,0),(6,1),(7,0),(7,1)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,3),(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4),(6,4)]
  | 81 => [(0,5),(1,2),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(5,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node130Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(0,0),(6,4)]
  | 2 => some [(1,2),(3,2),(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(8,0)]
  | 14 => some [(4,5),(7,3)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(5,4),(8,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,3),(7,1),(8,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,0),(0,1),(0,5),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(6,2),(7,2)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node130Domains1_fast_eq : root7Node130Domains1 = expandDomains root7Node130Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node130Domains1 v = expandDomains root7Node130Domains1Fast v from by decide) v
theorem root7Node130Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq (by decide)
theorem root7Node130Step1Narrowing_checked :
    checkNarrowing table21 root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root7Node130Domains0 root7Node130Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node130Step1Chunk0_0_checked, root7Node130Step1Chunk0_1_checked, root7Node130Step1Chunk0_2_checked, root7Node130Step1Chunk0_3_checked, root7Node130Step1Chunk0_4_checked, root7Node130Step1Chunk0_5_checked, root7Node130Step1Chunk1_0_checked, root7Node130Step1Chunk1_1_checked, root7Node130Step1Chunk1_2_checked, root7Node130Step1Chunk1_3_checked, root7Node130Step1Chunk1_4_checked, root7Node130Step1Chunk1_5_checked, root7Node130Step1Chunk2_0_checked, root7Node130Step1Chunk2_1_checked, root7Node130Step1Chunk2_2_checked, root7Node130Step1Chunk2_3_checked, root7Node130Step1Chunk2_4_checked, root7Node130Step1Chunk2_5_checked, root7Node130Step1Chunk3_0_checked, root7Node130Step1Chunk3_1_checked, root7Node130Step1Chunk3_2_checked, root7Node130Step1Chunk3_3_checked, root7Node130Step1Chunk3_4_checked, root7Node130Step1Chunk3_5_checked, root7Node130Step1Chunk4_0_checked, root7Node130Step1Chunk4_1_checked, root7Node130Step1Chunk4_2_checked, root7Node130Step1Chunk4_3_checked, root7Node130Step1Chunk4_4_checked, root7Node130Step1Chunk4_5_checked, root7Node130Step1Chunk5_0_checked, root7Node130Step1Chunk5_1_checked, root7Node130Step1Chunk5_2_checked, root7Node130Step1Chunk5_3_checked, root7Node130Step1Chunk5_4_checked, root7Node130Step1Chunk5_5_checked, root7Node130Step1Chunk6_0_checked, root7Node130Step1Chunk6_1_checked, root7Node130Step1Chunk6_2_checked, root7Node130Step1Chunk6_3_checked, root7Node130Step1Chunk6_4_checked, root7Node130Step1Chunk6_5_checked, root7Node130Step1Chunk7_0_checked, root7Node130Step1Chunk7_1_checked, root7Node130Step1Chunk7_2_checked, root7Node130Step1Chunk7_3_checked, root7Node130Step1Chunk7_4_checked, root7Node130Step1Chunk7_5_checked, root7Node130Step1Chunk8_0_checked, root7Node130Step1Chunk8_1_checked, root7Node130Step1Chunk8_2_checked, root7Node130Step1Chunk8_3_checked, root7Node130Step1Chunk8_4_checked, root7Node130Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node130Step1_checked :
    checkReplacement table21 root7Node130Domains0 root7Node130Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node130Domains0 root7Node130Domains1
    root7Node130Domains0Fast root7Node130Domains1Fast
    root7Node130Domains0_fast_eq root7Node130Domains1_fast_eq
    root7Node130Step1Narrowing_checked (by decide)
def root7Node131Domains0 : Domains 91 State := restrict root7Node130Domains1 1 (0,0)
def root7Node131Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(0,0)]
  | 2 => some [(1,2),(3,2),(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(8,0)]
  | 14 => some [(4,5),(7,3)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(5,4),(8,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,3),(7,1),(8,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,0),(0,1),(0,5),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(6,2),(7,2)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 71 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node131Domains0_fast_eq : root7Node131Domains0 = expandDomains root7Node131Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node131Domains0 v = expandDomains root7Node131Domains0Fast v from by decide) v
def root7Node131Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,3),(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4),(6,4)]
  | 81 => [(0,5),(1,2),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(5,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node131Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(0,0)]
  | 2 => some [(3,2),(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node131Domains1_fast_eq : root7Node131Domains1 = expandDomains root7Node131Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node131Domains1 v = expandDomains root7Node131Domains1Fast v from by decide) v
theorem root7Node131Step1Chunk0_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk0_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk0_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk0_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk0_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk0_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk1_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk1_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk1_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk1_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk1_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk1_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk2_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk2_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk2_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk2_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk2_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk2_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk3_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk3_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk3_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk3_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk3_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk3_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk4_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk4_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk4_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk4_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk4_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk4_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk5_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk5_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk5_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk5_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk5_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk5_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk6_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk6_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk6_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk6_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk6_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk6_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk7_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk7_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk7_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk7_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk7_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk7_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk8_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_0⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk8_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_1⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk8_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_2⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk8_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_3⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk8_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_4⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Chunk8_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_5⟩
      root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq (by decide)
theorem root7Node131Step1Narrowing_checked :
    checkNarrowing table32 root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkNarrowing_flatten table32Scope [table32Rows0_0,table32Rows0_1,table32Rows0_2,table32Rows0_3,table32Rows0_4,table32Rows0_5,table32Rows1_0,table32Rows1_1,table32Rows1_2,table32Rows1_3,table32Rows1_4,table32Rows1_5,table32Rows2_0,table32Rows2_1,table32Rows2_2,table32Rows2_3,table32Rows2_4,table32Rows2_5,table32Rows3_0,table32Rows3_1,table32Rows3_2,table32Rows3_3,table32Rows3_4,table32Rows3_5,table32Rows4_0,table32Rows4_1,table32Rows4_2,table32Rows4_3,table32Rows4_4,table32Rows4_5,table32Rows5_0,table32Rows5_1,table32Rows5_2,table32Rows5_3,table32Rows5_4,table32Rows5_5,table32Rows6_0,table32Rows6_1,table32Rows6_2,table32Rows6_3,table32Rows6_4,table32Rows6_5,table32Rows7_0,table32Rows7_1,table32Rows7_2,table32Rows7_3,table32Rows7_4,table32Rows7_5,table32Rows8_0,table32Rows8_1,table32Rows8_2,table32Rows8_3,table32Rows8_4,table32Rows8_5]
    root7Node131Domains0 root7Node131Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node131Step1Chunk0_0_checked, root7Node131Step1Chunk0_1_checked, root7Node131Step1Chunk0_2_checked, root7Node131Step1Chunk0_3_checked, root7Node131Step1Chunk0_4_checked, root7Node131Step1Chunk0_5_checked, root7Node131Step1Chunk1_0_checked, root7Node131Step1Chunk1_1_checked, root7Node131Step1Chunk1_2_checked, root7Node131Step1Chunk1_3_checked, root7Node131Step1Chunk1_4_checked, root7Node131Step1Chunk1_5_checked, root7Node131Step1Chunk2_0_checked, root7Node131Step1Chunk2_1_checked, root7Node131Step1Chunk2_2_checked, root7Node131Step1Chunk2_3_checked, root7Node131Step1Chunk2_4_checked, root7Node131Step1Chunk2_5_checked, root7Node131Step1Chunk3_0_checked, root7Node131Step1Chunk3_1_checked, root7Node131Step1Chunk3_2_checked, root7Node131Step1Chunk3_3_checked, root7Node131Step1Chunk3_4_checked, root7Node131Step1Chunk3_5_checked, root7Node131Step1Chunk4_0_checked, root7Node131Step1Chunk4_1_checked, root7Node131Step1Chunk4_2_checked, root7Node131Step1Chunk4_3_checked, root7Node131Step1Chunk4_4_checked, root7Node131Step1Chunk4_5_checked, root7Node131Step1Chunk5_0_checked, root7Node131Step1Chunk5_1_checked, root7Node131Step1Chunk5_2_checked, root7Node131Step1Chunk5_3_checked, root7Node131Step1Chunk5_4_checked, root7Node131Step1Chunk5_5_checked, root7Node131Step1Chunk6_0_checked, root7Node131Step1Chunk6_1_checked, root7Node131Step1Chunk6_2_checked, root7Node131Step1Chunk6_3_checked, root7Node131Step1Chunk6_4_checked, root7Node131Step1Chunk6_5_checked, root7Node131Step1Chunk7_0_checked, root7Node131Step1Chunk7_1_checked, root7Node131Step1Chunk7_2_checked, root7Node131Step1Chunk7_3_checked, root7Node131Step1Chunk7_4_checked, root7Node131Step1Chunk7_5_checked, root7Node131Step1Chunk8_0_checked, root7Node131Step1Chunk8_1_checked, root7Node131Step1Chunk8_2_checked, root7Node131Step1Chunk8_3_checked, root7Node131Step1Chunk8_4_checked, root7Node131Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node131Step1_checked :
    checkReplacement table32 root7Node131Domains0 root7Node131Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node131Domains0 root7Node131Domains1
    root7Node131Domains0Fast root7Node131Domains1Fast
    root7Node131Domains0_fast_eq root7Node131Domains1_fast_eq
    root7Node131Step1Narrowing_checked (by decide)
def root7Node131Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(0,0)]
  | 2 => [(3,2),(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(5,0),(8,0)]
  | 28 => [(4,5),(7,3)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node131Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(0,0)]
  | 2 => some [(3,2),(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node131Domains2_fast_eq : root7Node131Domains2 = expandDomains root7Node131Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node131Domains2 v = expandDomains root7Node131Domains2Fast v from by decide) v
theorem root7Node131Step2Chunk0_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk0_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk0_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk0_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk0_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk0_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk1_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk1_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk1_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk1_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk1_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk1_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk2_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk2_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk2_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk2_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk2_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk2_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk3_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk3_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk3_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk3_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk3_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk3_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk4_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk4_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk4_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk4_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk4_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk4_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk5_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk5_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk5_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk5_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk5_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk5_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk6_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk6_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk6_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk6_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk6_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk6_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk7_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk7_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk7_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk7_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk7_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk7_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk8_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_0⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk8_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_1⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk8_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_2⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk8_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_3⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk8_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_4⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Chunk8_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_5⟩
      root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq (by decide)
theorem root7Node131Step2Narrowing_checked :
    checkNarrowing table53 root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkNarrowing_flatten table53Scope [table53Rows0_0,table53Rows0_1,table53Rows0_2,table53Rows0_3,table53Rows0_4,table53Rows0_5,table53Rows1_0,table53Rows1_1,table53Rows1_2,table53Rows1_3,table53Rows1_4,table53Rows1_5,table53Rows2_0,table53Rows2_1,table53Rows2_2,table53Rows2_3,table53Rows2_4,table53Rows2_5,table53Rows3_0,table53Rows3_1,table53Rows3_2,table53Rows3_3,table53Rows3_4,table53Rows3_5,table53Rows4_0,table53Rows4_1,table53Rows4_2,table53Rows4_3,table53Rows4_4,table53Rows4_5,table53Rows5_0,table53Rows5_1,table53Rows5_2,table53Rows5_3,table53Rows5_4,table53Rows5_5,table53Rows6_0,table53Rows6_1,table53Rows6_2,table53Rows6_3,table53Rows6_4,table53Rows6_5,table53Rows7_0,table53Rows7_1,table53Rows7_2,table53Rows7_3,table53Rows7_4,table53Rows7_5,table53Rows8_0,table53Rows8_1,table53Rows8_2,table53Rows8_3,table53Rows8_4,table53Rows8_5]
    root7Node131Domains1 root7Node131Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node131Step2Chunk0_0_checked, root7Node131Step2Chunk0_1_checked, root7Node131Step2Chunk0_2_checked, root7Node131Step2Chunk0_3_checked, root7Node131Step2Chunk0_4_checked, root7Node131Step2Chunk0_5_checked, root7Node131Step2Chunk1_0_checked, root7Node131Step2Chunk1_1_checked, root7Node131Step2Chunk1_2_checked, root7Node131Step2Chunk1_3_checked, root7Node131Step2Chunk1_4_checked, root7Node131Step2Chunk1_5_checked, root7Node131Step2Chunk2_0_checked, root7Node131Step2Chunk2_1_checked, root7Node131Step2Chunk2_2_checked, root7Node131Step2Chunk2_3_checked, root7Node131Step2Chunk2_4_checked, root7Node131Step2Chunk2_5_checked, root7Node131Step2Chunk3_0_checked, root7Node131Step2Chunk3_1_checked, root7Node131Step2Chunk3_2_checked, root7Node131Step2Chunk3_3_checked, root7Node131Step2Chunk3_4_checked, root7Node131Step2Chunk3_5_checked, root7Node131Step2Chunk4_0_checked, root7Node131Step2Chunk4_1_checked, root7Node131Step2Chunk4_2_checked, root7Node131Step2Chunk4_3_checked, root7Node131Step2Chunk4_4_checked, root7Node131Step2Chunk4_5_checked, root7Node131Step2Chunk5_0_checked, root7Node131Step2Chunk5_1_checked, root7Node131Step2Chunk5_2_checked, root7Node131Step2Chunk5_3_checked, root7Node131Step2Chunk5_4_checked, root7Node131Step2Chunk5_5_checked, root7Node131Step2Chunk6_0_checked, root7Node131Step2Chunk6_1_checked, root7Node131Step2Chunk6_2_checked, root7Node131Step2Chunk6_3_checked, root7Node131Step2Chunk6_4_checked, root7Node131Step2Chunk6_5_checked, root7Node131Step2Chunk7_0_checked, root7Node131Step2Chunk7_1_checked, root7Node131Step2Chunk7_2_checked, root7Node131Step2Chunk7_3_checked, root7Node131Step2Chunk7_4_checked, root7Node131Step2Chunk7_5_checked, root7Node131Step2Chunk8_0_checked, root7Node131Step2Chunk8_1_checked, root7Node131Step2Chunk8_2_checked, root7Node131Step2Chunk8_3_checked, root7Node131Step2Chunk8_4_checked, root7Node131Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node131Step2_checked :
    checkReplacement table53 root7Node131Domains1 root7Node131Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node131Domains1 root7Node131Domains2
    root7Node131Domains1Fast root7Node131Domains2Fast
    root7Node131Domains1_fast_eq root7Node131Domains2_fast_eq
    root7Node131Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
