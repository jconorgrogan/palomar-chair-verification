module

public import SpectreFinite.RadiusFiveRoot8Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable43
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node10Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(6,2)]
  | 12 => [(5,4),(8,4)]
  | 13 => [(5,0),(5,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(6,3),(7,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(3,4),(7,4)]
  | 40 => [(0,0),(1,4),(6,4)]
  | 41 => [(0,5),(1,2),(3,2)]
  | 42 => [(2,0),(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,5)]
  | 50 => [(0,2),(1,0),(6,0)]
  | 51 => [(0,3),(6,0),(6,1)]
  | 52 => [(3,1),(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(3,2),(7,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0),(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4),(8,4)]
  | 83 => [(0,0),(6,3),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(7,5)]
  | _ => [(0,3),(1,1),(6,1)]
def root8Node10Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(5,4),(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,5)]
  | 50 => some [(0,2),(1,0),(6,0)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(7,5)]
  | _ => some [(0,3),(1,1),(6,1)]
theorem root8Node10Domains4_fast_eq : root8Node10Domains4 = expandDomains root8Node10Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node10Domains4 v = expandDomains root8Node10Domains4Fast v from by decide) v
theorem root8Node10Step4Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq (by decide)
theorem root8Node10Step4Narrowing_checked :
    checkNarrowing table12 root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root8Node10Domains3 root8Node10Domains4 (by
      simp only [List.all_cons, List.all_nil, root8Node10Step4Chunk0_0_checked, root8Node10Step4Chunk0_1_checked, root8Node10Step4Chunk0_2_checked, root8Node10Step4Chunk0_3_checked, root8Node10Step4Chunk0_4_checked, root8Node10Step4Chunk0_5_checked, root8Node10Step4Chunk1_0_checked, root8Node10Step4Chunk1_1_checked, root8Node10Step4Chunk1_2_checked, root8Node10Step4Chunk1_3_checked, root8Node10Step4Chunk1_4_checked, root8Node10Step4Chunk1_5_checked, root8Node10Step4Chunk2_0_checked, root8Node10Step4Chunk2_1_checked, root8Node10Step4Chunk2_2_checked, root8Node10Step4Chunk2_3_checked, root8Node10Step4Chunk2_4_checked, root8Node10Step4Chunk2_5_checked, root8Node10Step4Chunk3_0_checked, root8Node10Step4Chunk3_1_checked, root8Node10Step4Chunk3_2_checked, root8Node10Step4Chunk3_3_checked, root8Node10Step4Chunk3_4_checked, root8Node10Step4Chunk3_5_checked, root8Node10Step4Chunk4_0_checked, root8Node10Step4Chunk4_1_checked, root8Node10Step4Chunk4_2_checked, root8Node10Step4Chunk4_3_checked, root8Node10Step4Chunk4_4_checked, root8Node10Step4Chunk4_5_checked, root8Node10Step4Chunk5_0_checked, root8Node10Step4Chunk5_1_checked, root8Node10Step4Chunk5_2_checked, root8Node10Step4Chunk5_3_checked, root8Node10Step4Chunk5_4_checked, root8Node10Step4Chunk5_5_checked, root8Node10Step4Chunk6_0_checked, root8Node10Step4Chunk6_1_checked, root8Node10Step4Chunk6_2_checked, root8Node10Step4Chunk6_3_checked, root8Node10Step4Chunk6_4_checked, root8Node10Step4Chunk6_5_checked, root8Node10Step4Chunk7_0_checked, root8Node10Step4Chunk7_1_checked, root8Node10Step4Chunk7_2_checked, root8Node10Step4Chunk7_3_checked, root8Node10Step4Chunk7_4_checked, root8Node10Step4Chunk7_5_checked, root8Node10Step4Chunk8_0_checked, root8Node10Step4Chunk8_1_checked, root8Node10Step4Chunk8_2_checked, root8Node10Step4Chunk8_3_checked, root8Node10Step4Chunk8_4_checked, root8Node10Step4Chunk8_5_checked, Bool.true_and])
theorem root8Node10Step4_checked :
    checkReplacement table12 root8Node10Domains3 root8Node10Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root8Node10Domains3 root8Node10Domains4
    root8Node10Domains3Fast root8Node10Domains4Fast
    root8Node10Domains3_fast_eq root8Node10Domains4_fast_eq
    root8Node10Step4Narrowing_checked (by decide)
def root8Node11Domains0 : Domains 91 State := restrict root8Node10Domains4 3 (4,0)
def root8Node11Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(5,4),(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,5)]
  | 50 => some [(0,2),(1,0),(6,0)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(7,5)]
  | _ => some [(0,3),(1,1),(6,1)]
theorem root8Node11Domains0_fast_eq : root8Node11Domains0 = expandDomains root8Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node11Domains0 v = expandDomains root8Node11Domains0Fast v from by decide) v
def root8Node11Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0),(5,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(0,0),(1,4),(6,4)]
  | 41 => [(0,5),(1,2),(3,2)]
  | 42 => [(2,0),(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(0,3),(6,0),(6,1)]
  | 52 => [(3,1),(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0),(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4),(8,4)]
  | 83 => [(0,0),(6,3),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(7,5)]
  | _ => [(0,3),(1,1),(6,1)]
def root8Node11Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(7,5)]
  | _ => some [(0,3),(1,1),(6,1)]
theorem root8Node11Domains1_fast_eq : root8Node11Domains1 = expandDomains root8Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node11Domains1 v = expandDomains root8Node11Domains1Fast v from by decide) v
theorem root8Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq (by decide)
theorem root8Node11Step1Narrowing_checked :
    checkNarrowing table36 root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root8Node11Domains0 root8Node11Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node11Step1Chunk0_0_checked, root8Node11Step1Chunk0_1_checked, root8Node11Step1Chunk0_2_checked, root8Node11Step1Chunk0_3_checked, root8Node11Step1Chunk0_4_checked, root8Node11Step1Chunk0_5_checked, root8Node11Step1Chunk1_0_checked, root8Node11Step1Chunk1_1_checked, root8Node11Step1Chunk1_2_checked, root8Node11Step1Chunk1_3_checked, root8Node11Step1Chunk1_4_checked, root8Node11Step1Chunk1_5_checked, root8Node11Step1Chunk2_0_checked, root8Node11Step1Chunk2_1_checked, root8Node11Step1Chunk2_2_checked, root8Node11Step1Chunk2_3_checked, root8Node11Step1Chunk2_4_checked, root8Node11Step1Chunk2_5_checked, root8Node11Step1Chunk3_0_checked, root8Node11Step1Chunk3_1_checked, root8Node11Step1Chunk3_2_checked, root8Node11Step1Chunk3_3_checked, root8Node11Step1Chunk3_4_checked, root8Node11Step1Chunk3_5_checked, root8Node11Step1Chunk4_0_checked, root8Node11Step1Chunk4_1_checked, root8Node11Step1Chunk4_2_checked, root8Node11Step1Chunk4_3_checked, root8Node11Step1Chunk4_4_checked, root8Node11Step1Chunk4_5_checked, root8Node11Step1Chunk5_0_checked, root8Node11Step1Chunk5_1_checked, root8Node11Step1Chunk5_2_checked, root8Node11Step1Chunk5_3_checked, root8Node11Step1Chunk5_4_checked, root8Node11Step1Chunk5_5_checked, root8Node11Step1Chunk6_0_checked, root8Node11Step1Chunk6_1_checked, root8Node11Step1Chunk6_2_checked, root8Node11Step1Chunk6_3_checked, root8Node11Step1Chunk6_4_checked, root8Node11Step1Chunk6_5_checked, root8Node11Step1Chunk7_0_checked, root8Node11Step1Chunk7_1_checked, root8Node11Step1Chunk7_2_checked, root8Node11Step1Chunk7_3_checked, root8Node11Step1Chunk7_4_checked, root8Node11Step1Chunk7_5_checked, root8Node11Step1Chunk8_0_checked, root8Node11Step1Chunk8_1_checked, root8Node11Step1Chunk8_2_checked, root8Node11Step1Chunk8_3_checked, root8Node11Step1Chunk8_4_checked, root8Node11Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node11Step1_checked :
    checkReplacement table36 root8Node11Domains0 root8Node11Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node11Domains0 root8Node11Domains1
    root8Node11Domains0Fast root8Node11Domains1Fast
    root8Node11Domains0_fast_eq root8Node11Domains1_fast_eq
    root8Node11Step1Narrowing_checked (by decide)
def root8Node11Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0),(5,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(0,0),(1,4),(6,4)]
  | 41 => [(0,5),(1,2),(3,2)]
  | 42 => [(2,0),(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(0,3),(6,0),(6,1)]
  | 52 => [(3,1),(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0),(1,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(6,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node11Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(1,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node11Domains2_fast_eq : root8Node11Domains2 = expandDomains root8Node11Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node11Domains2 v = expandDomains root8Node11Domains2Fast v from by decide) v
theorem root8Node11Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq (by decide)
theorem root8Node11Step2Narrowing_checked :
    checkNarrowing table65 root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root8Node11Domains1 root8Node11Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node11Step2Chunk0_0_checked, root8Node11Step2Chunk0_1_checked, root8Node11Step2Chunk0_2_checked, root8Node11Step2Chunk0_3_checked, root8Node11Step2Chunk0_4_checked, root8Node11Step2Chunk0_5_checked, root8Node11Step2Chunk1_0_checked, root8Node11Step2Chunk1_1_checked, root8Node11Step2Chunk1_2_checked, root8Node11Step2Chunk1_3_checked, root8Node11Step2Chunk1_4_checked, root8Node11Step2Chunk1_5_checked, root8Node11Step2Chunk2_0_checked, root8Node11Step2Chunk2_1_checked, root8Node11Step2Chunk2_2_checked, root8Node11Step2Chunk2_3_checked, root8Node11Step2Chunk2_4_checked, root8Node11Step2Chunk2_5_checked, root8Node11Step2Chunk3_0_checked, root8Node11Step2Chunk3_1_checked, root8Node11Step2Chunk3_2_checked, root8Node11Step2Chunk3_3_checked, root8Node11Step2Chunk3_4_checked, root8Node11Step2Chunk3_5_checked, root8Node11Step2Chunk4_0_checked, root8Node11Step2Chunk4_1_checked, root8Node11Step2Chunk4_2_checked, root8Node11Step2Chunk4_3_checked, root8Node11Step2Chunk4_4_checked, root8Node11Step2Chunk4_5_checked, root8Node11Step2Chunk5_0_checked, root8Node11Step2Chunk5_1_checked, root8Node11Step2Chunk5_2_checked, root8Node11Step2Chunk5_3_checked, root8Node11Step2Chunk5_4_checked, root8Node11Step2Chunk5_5_checked, root8Node11Step2Chunk6_0_checked, root8Node11Step2Chunk6_1_checked, root8Node11Step2Chunk6_2_checked, root8Node11Step2Chunk6_3_checked, root8Node11Step2Chunk6_4_checked, root8Node11Step2Chunk6_5_checked, root8Node11Step2Chunk7_0_checked, root8Node11Step2Chunk7_1_checked, root8Node11Step2Chunk7_2_checked, root8Node11Step2Chunk7_3_checked, root8Node11Step2Chunk7_4_checked, root8Node11Step2Chunk7_5_checked, root8Node11Step2Chunk8_0_checked, root8Node11Step2Chunk8_1_checked, root8Node11Step2Chunk8_2_checked, root8Node11Step2Chunk8_3_checked, root8Node11Step2Chunk8_4_checked, root8Node11Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node11Step2_checked :
    checkReplacement table65 root8Node11Domains1 root8Node11Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node11Domains1 root8Node11Domains2
    root8Node11Domains1Fast root8Node11Domains2Fast
    root8Node11Domains1_fast_eq root8Node11Domains2_fast_eq
    root8Node11Step2Narrowing_checked (by decide)
def root8Node12Domains0 : Domains 91 State := restrict root8Node11Domains2 6 (7,1)
def root8Node12Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0),(1,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node12Domains0_fast_eq : root8Node12Domains0 = expandDomains root8Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node12Domains0 v = expandDomains root8Node12Domains0Fast v from by decide) v
def root8Node12Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
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
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(4,3)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(7,4)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(1,0)]
  | 49 => [(2,1)]
  | 50 => [(0,2)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(3,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node12Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
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
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(1,0)]
  | 49 => some [(2,1)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(3,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node12Domains1_fast_eq : root8Node12Domains1 = expandDomains root8Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node12Domains1 v = expandDomains root8Node12Domains1Fast v from by decide) v
theorem root8Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows0_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows1_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows2_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows3_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows4_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows5_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows6_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows7_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_0⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_1⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_2⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_3⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_4⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table43Scope, table43Rows8_5⟩
      root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq (by decide)
theorem root8Node12Step1Narrowing_checked :
    checkNarrowing table43 root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkNarrowing_flatten table43Scope [table43Rows0_0,table43Rows0_1,table43Rows0_2,table43Rows0_3,table43Rows0_4,table43Rows0_5,table43Rows1_0,table43Rows1_1,table43Rows1_2,table43Rows1_3,table43Rows1_4,table43Rows1_5,table43Rows2_0,table43Rows2_1,table43Rows2_2,table43Rows2_3,table43Rows2_4,table43Rows2_5,table43Rows3_0,table43Rows3_1,table43Rows3_2,table43Rows3_3,table43Rows3_4,table43Rows3_5,table43Rows4_0,table43Rows4_1,table43Rows4_2,table43Rows4_3,table43Rows4_4,table43Rows4_5,table43Rows5_0,table43Rows5_1,table43Rows5_2,table43Rows5_3,table43Rows5_4,table43Rows5_5,table43Rows6_0,table43Rows6_1,table43Rows6_2,table43Rows6_3,table43Rows6_4,table43Rows6_5,table43Rows7_0,table43Rows7_1,table43Rows7_2,table43Rows7_3,table43Rows7_4,table43Rows7_5,table43Rows8_0,table43Rows8_1,table43Rows8_2,table43Rows8_3,table43Rows8_4,table43Rows8_5]
    root8Node12Domains0 root8Node12Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node12Step1Chunk0_0_checked, root8Node12Step1Chunk0_1_checked, root8Node12Step1Chunk0_2_checked, root8Node12Step1Chunk0_3_checked, root8Node12Step1Chunk0_4_checked, root8Node12Step1Chunk0_5_checked, root8Node12Step1Chunk1_0_checked, root8Node12Step1Chunk1_1_checked, root8Node12Step1Chunk1_2_checked, root8Node12Step1Chunk1_3_checked, root8Node12Step1Chunk1_4_checked, root8Node12Step1Chunk1_5_checked, root8Node12Step1Chunk2_0_checked, root8Node12Step1Chunk2_1_checked, root8Node12Step1Chunk2_2_checked, root8Node12Step1Chunk2_3_checked, root8Node12Step1Chunk2_4_checked, root8Node12Step1Chunk2_5_checked, root8Node12Step1Chunk3_0_checked, root8Node12Step1Chunk3_1_checked, root8Node12Step1Chunk3_2_checked, root8Node12Step1Chunk3_3_checked, root8Node12Step1Chunk3_4_checked, root8Node12Step1Chunk3_5_checked, root8Node12Step1Chunk4_0_checked, root8Node12Step1Chunk4_1_checked, root8Node12Step1Chunk4_2_checked, root8Node12Step1Chunk4_3_checked, root8Node12Step1Chunk4_4_checked, root8Node12Step1Chunk4_5_checked, root8Node12Step1Chunk5_0_checked, root8Node12Step1Chunk5_1_checked, root8Node12Step1Chunk5_2_checked, root8Node12Step1Chunk5_3_checked, root8Node12Step1Chunk5_4_checked, root8Node12Step1Chunk5_5_checked, root8Node12Step1Chunk6_0_checked, root8Node12Step1Chunk6_1_checked, root8Node12Step1Chunk6_2_checked, root8Node12Step1Chunk6_3_checked, root8Node12Step1Chunk6_4_checked, root8Node12Step1Chunk6_5_checked, root8Node12Step1Chunk7_0_checked, root8Node12Step1Chunk7_1_checked, root8Node12Step1Chunk7_2_checked, root8Node12Step1Chunk7_3_checked, root8Node12Step1Chunk7_4_checked, root8Node12Step1Chunk7_5_checked, root8Node12Step1Chunk8_0_checked, root8Node12Step1Chunk8_1_checked, root8Node12Step1Chunk8_2_checked, root8Node12Step1Chunk8_3_checked, root8Node12Step1Chunk8_4_checked, root8Node12Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node12Step1_checked :
    checkReplacement table43 root8Node12Domains0 root8Node12Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node12Domains0 root8Node12Domains1
    root8Node12Domains0Fast root8Node12Domains1Fast
    root8Node12Domains0_fast_eq root8Node12Domains1_fast_eq
    root8Node12Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
