module

public import SpectreFinite.RadiusFiveRoot6Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable2
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node14Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2),(5,2),(7,0),(8,2)]
  | 1 => [(4,3),(5,0),(5,3),(8,3)]
  | 2 => [(4,5),(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0)]
  | 4 => [(4,3),(7,1),(8,3)]
  | 5 => [(1,5),(4,5),(7,5),(8,5)]
  | 6 => [(1,2),(7,2)]
  | 7 => [(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0)]
  | 11 => [(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(7,2),(8,2)]
  | 13 => [(0,3),(1,1),(6,1)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(1,5),(6,5)]
  | 16 => [(0,4),(1,1),(6,1)]
  | 17 => [(5,1),(5,4),(8,1)]
  | 18 => [(0,0),(0,1),(6,4),(6,5)]
  | 19 => [(0,4),(1,2),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,4),(7,4)]
  | 21 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(8,0)]
  | 22 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => [(0,2),(1,5),(3,5),(6,0)]
  | 30 => [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(7,1),(8,4)]
  | 31 => [(0,1),(1,4),(6,5)]
  | 32 => [(0,4),(0,5),(6,2)]
  | 33 => [(4,4),(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(8,0)]
  | 40 => [(3,0),(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => [(2,5),(4,5),(7,5),(8,5)]
  | 42 => [(1,0),(6,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5),(7,5)]
  | 48 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(6,4),(6,5)]
  | 51 => [(0,0),(1,3),(7,3)]
  | 52 => [(7,2),(8,2)]
  | 53 => [(4,0),(7,4),(8,0)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(1,0),(4,2),(7,0),(8,2)]
  | 59 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => [(4,5),(7,5),(8,5)]
  | 61 => [(0,4),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(8,1),(8,4)]
  | 63 => [(0,1),(6,4),(6,5)]
  | 64 => [(0,4),(1,2),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0),(6,4)]
  | 67 => [(1,2),(7,2)]
  | 68 => [(4,0),(7,4),(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(7,3)]
  | 70 => [(4,3),(7,1),(8,3)]
  | 71 => [(5,5),(7,5),(8,5)]
  | 72 => [(0,3),(1,0),(7,0)]
  | 73 => [(4,3),(7,1),(8,1)]
  | 74 => [(1,5),(3,5),(7,5)]
  | 75 => [(0,3),(6,1)]
  | 76 => [(4,1),(5,1),(8,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5)]
  | 78 => [(0,5),(1,3),(6,3),(7,3)]
  | 79 => [(4,2),(4,4),(7,2),(8,2)]
  | 80 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(1,3),(6,2),(6,3)]
def root6Node14Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(4,5),(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(4,5),(7,5),(8,5)]
  | 6 => some [(1,2),(7,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(7,2),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5)]
  | 16 => some [(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(8,0)]
  | 22 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(7,1),(8,4)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(2,5),(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(7,4),(8,0)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,1),(8,4)]
  | 63 => some [(0,1),(6,4),(6,5)]
  | 64 => some [(0,4),(1,2),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(5,5),(7,5),(8,5)]
  | 72 => some [(0,3),(1,0),(7,0)]
  | 73 => some [(4,3),(7,1),(8,1)]
  | 74 => some [(1,5),(3,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(1,3),(6,2),(6,3)]
theorem root6Node14Domains3_fast_eq : root6Node14Domains3 = expandDomains root6Node14Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node14Domains3 v = expandDomains root6Node14Domains3Fast v from by decide) v
theorem root6Node14Step3Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq (by decide)
theorem root6Node14Step3Narrowing_checked :
    checkNarrowing table51 root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root6Node14Domains2 root6Node14Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node14Step3Chunk0_0_checked, root6Node14Step3Chunk0_1_checked, root6Node14Step3Chunk0_2_checked, root6Node14Step3Chunk0_3_checked, root6Node14Step3Chunk0_4_checked, root6Node14Step3Chunk0_5_checked, root6Node14Step3Chunk1_0_checked, root6Node14Step3Chunk1_1_checked, root6Node14Step3Chunk1_2_checked, root6Node14Step3Chunk1_3_checked, root6Node14Step3Chunk1_4_checked, root6Node14Step3Chunk1_5_checked, root6Node14Step3Chunk2_0_checked, root6Node14Step3Chunk2_1_checked, root6Node14Step3Chunk2_2_checked, root6Node14Step3Chunk2_3_checked, root6Node14Step3Chunk2_4_checked, root6Node14Step3Chunk2_5_checked, root6Node14Step3Chunk3_0_checked, root6Node14Step3Chunk3_1_checked, root6Node14Step3Chunk3_2_checked, root6Node14Step3Chunk3_3_checked, root6Node14Step3Chunk3_4_checked, root6Node14Step3Chunk3_5_checked, root6Node14Step3Chunk4_0_checked, root6Node14Step3Chunk4_1_checked, root6Node14Step3Chunk4_2_checked, root6Node14Step3Chunk4_3_checked, root6Node14Step3Chunk4_4_checked, root6Node14Step3Chunk4_5_checked, root6Node14Step3Chunk5_0_checked, root6Node14Step3Chunk5_1_checked, root6Node14Step3Chunk5_2_checked, root6Node14Step3Chunk5_3_checked, root6Node14Step3Chunk5_4_checked, root6Node14Step3Chunk5_5_checked, root6Node14Step3Chunk6_0_checked, root6Node14Step3Chunk6_1_checked, root6Node14Step3Chunk6_2_checked, root6Node14Step3Chunk6_3_checked, root6Node14Step3Chunk6_4_checked, root6Node14Step3Chunk6_5_checked, root6Node14Step3Chunk7_0_checked, root6Node14Step3Chunk7_1_checked, root6Node14Step3Chunk7_2_checked, root6Node14Step3Chunk7_3_checked, root6Node14Step3Chunk7_4_checked, root6Node14Step3Chunk7_5_checked, root6Node14Step3Chunk8_0_checked, root6Node14Step3Chunk8_1_checked, root6Node14Step3Chunk8_2_checked, root6Node14Step3Chunk8_3_checked, root6Node14Step3Chunk8_4_checked, root6Node14Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node14Step3_checked :
    checkReplacement table51 root6Node14Domains2 root6Node14Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node14Domains2 root6Node14Domains3
    root6Node14Domains2Fast root6Node14Domains3Fast
    root6Node14Domains2_fast_eq root6Node14Domains3_fast_eq
    root6Node14Step3Narrowing_checked (by decide)
def root6Node14Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2),(5,2),(7,0),(8,2)]
  | 1 => [(4,3),(5,0),(5,3),(8,3)]
  | 2 => [(4,5),(7,5),(8,5)]
  | 3 => [(1,0),(6,0),(7,0)]
  | 4 => [(4,3),(7,1),(8,3)]
  | 5 => [(1,5),(7,5),(8,5)]
  | 6 => [(1,2),(7,2)]
  | 7 => [(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0)]
  | 11 => [(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(8,2)]
  | 13 => [(0,3),(1,1),(6,1)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(1,5),(6,5)]
  | 16 => [(0,4),(1,1),(6,1)]
  | 17 => [(5,1),(5,4),(8,1)]
  | 18 => [(0,0),(0,1),(6,4),(6,5)]
  | 19 => [(0,4),(1,2),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,4),(7,4)]
  | 21 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(8,0)]
  | 22 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => [(0,2),(1,5),(3,5),(6,0)]
  | 30 => [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(7,1),(8,4)]
  | 31 => [(0,1),(1,4),(6,5)]
  | 32 => [(0,4),(0,5),(6,2)]
  | 33 => [(4,4),(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(8,0)]
  | 40 => [(3,0),(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => [(2,5),(4,5),(7,5),(8,5)]
  | 42 => [(1,0),(6,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5),(7,5)]
  | 48 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(6,4),(6,5)]
  | 51 => [(0,0),(1,3),(7,3)]
  | 52 => [(7,2),(8,2)]
  | 53 => [(4,0),(7,4),(8,0)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(1,0),(4,2),(7,0),(8,2)]
  | 59 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => [(4,5),(7,5),(8,5)]
  | 61 => [(0,4),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(8,1),(8,4)]
  | 63 => [(0,1),(6,4),(6,5)]
  | 64 => [(0,4),(1,2),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0),(6,4)]
  | 67 => [(1,2),(7,2)]
  | 68 => [(4,0),(7,4),(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(7,3)]
  | 70 => [(4,3),(7,1),(8,3)]
  | 71 => [(5,5),(7,5),(8,5)]
  | 72 => [(0,3),(1,0),(7,0)]
  | 73 => [(4,3),(7,1),(8,1)]
  | 74 => [(1,5),(3,5),(7,5)]
  | 75 => [(0,3),(6,1)]
  | 76 => [(4,1),(5,1),(8,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5)]
  | 78 => [(0,5),(1,3),(6,3),(7,3)]
  | 79 => [(4,2),(4,4),(7,2),(8,2)]
  | 80 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(1,3),(6,2),(6,3)]
def root6Node14Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(4,5),(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(7,5),(8,5)]
  | 6 => some [(1,2),(7,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5)]
  | 16 => some [(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(8,0)]
  | 22 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(7,1),(8,4)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(2,5),(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(7,4),(8,0)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,1),(8,4)]
  | 63 => some [(0,1),(6,4),(6,5)]
  | 64 => some [(0,4),(1,2),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(5,5),(7,5),(8,5)]
  | 72 => some [(0,3),(1,0),(7,0)]
  | 73 => some [(4,3),(7,1),(8,1)]
  | 74 => some [(1,5),(3,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(1,3),(6,2),(6,3)]
theorem root6Node14Domains4_fast_eq : root6Node14Domains4 = expandDomains root6Node14Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node14Domains4 v = expandDomains root6Node14Domains4Fast v from by decide) v
theorem root6Node14Step4Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq (by decide)
theorem root6Node14Step4Narrowing_checked :
    checkNarrowing table2 root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkNarrowing_flatten table2Scope [table2Rows0_0,table2Rows0_1,table2Rows0_2,table2Rows0_3,table2Rows0_4,table2Rows0_5,table2Rows1_0,table2Rows1_1,table2Rows1_2,table2Rows1_3,table2Rows1_4,table2Rows1_5,table2Rows2_0,table2Rows2_1,table2Rows2_2,table2Rows2_3,table2Rows2_4,table2Rows2_5,table2Rows3_0,table2Rows3_1,table2Rows3_2,table2Rows3_3,table2Rows3_4,table2Rows3_5,table2Rows4_0,table2Rows4_1,table2Rows4_2,table2Rows4_3,table2Rows4_4,table2Rows4_5,table2Rows5_0,table2Rows5_1,table2Rows5_2,table2Rows5_3,table2Rows5_4,table2Rows5_5,table2Rows6_0,table2Rows6_1,table2Rows6_2,table2Rows6_3,table2Rows6_4,table2Rows6_5,table2Rows7_0,table2Rows7_1,table2Rows7_2,table2Rows7_3,table2Rows7_4,table2Rows7_5,table2Rows8_0,table2Rows8_1,table2Rows8_2,table2Rows8_3,table2Rows8_4,table2Rows8_5]
    root6Node14Domains3 root6Node14Domains4 (by
      simp only [List.all_cons, List.all_nil, root6Node14Step4Chunk0_0_checked, root6Node14Step4Chunk0_1_checked, root6Node14Step4Chunk0_2_checked, root6Node14Step4Chunk0_3_checked, root6Node14Step4Chunk0_4_checked, root6Node14Step4Chunk0_5_checked, root6Node14Step4Chunk1_0_checked, root6Node14Step4Chunk1_1_checked, root6Node14Step4Chunk1_2_checked, root6Node14Step4Chunk1_3_checked, root6Node14Step4Chunk1_4_checked, root6Node14Step4Chunk1_5_checked, root6Node14Step4Chunk2_0_checked, root6Node14Step4Chunk2_1_checked, root6Node14Step4Chunk2_2_checked, root6Node14Step4Chunk2_3_checked, root6Node14Step4Chunk2_4_checked, root6Node14Step4Chunk2_5_checked, root6Node14Step4Chunk3_0_checked, root6Node14Step4Chunk3_1_checked, root6Node14Step4Chunk3_2_checked, root6Node14Step4Chunk3_3_checked, root6Node14Step4Chunk3_4_checked, root6Node14Step4Chunk3_5_checked, root6Node14Step4Chunk4_0_checked, root6Node14Step4Chunk4_1_checked, root6Node14Step4Chunk4_2_checked, root6Node14Step4Chunk4_3_checked, root6Node14Step4Chunk4_4_checked, root6Node14Step4Chunk4_5_checked, root6Node14Step4Chunk5_0_checked, root6Node14Step4Chunk5_1_checked, root6Node14Step4Chunk5_2_checked, root6Node14Step4Chunk5_3_checked, root6Node14Step4Chunk5_4_checked, root6Node14Step4Chunk5_5_checked, root6Node14Step4Chunk6_0_checked, root6Node14Step4Chunk6_1_checked, root6Node14Step4Chunk6_2_checked, root6Node14Step4Chunk6_3_checked, root6Node14Step4Chunk6_4_checked, root6Node14Step4Chunk6_5_checked, root6Node14Step4Chunk7_0_checked, root6Node14Step4Chunk7_1_checked, root6Node14Step4Chunk7_2_checked, root6Node14Step4Chunk7_3_checked, root6Node14Step4Chunk7_4_checked, root6Node14Step4Chunk7_5_checked, root6Node14Step4Chunk8_0_checked, root6Node14Step4Chunk8_1_checked, root6Node14Step4Chunk8_2_checked, root6Node14Step4Chunk8_3_checked, root6Node14Step4Chunk8_4_checked, root6Node14Step4Chunk8_5_checked, Bool.true_and])
theorem root6Node14Step4_checked :
    checkReplacement table2 root6Node14Domains3 root6Node14Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root6Node14Domains3 root6Node14Domains4
    root6Node14Domains3Fast root6Node14Domains4Fast
    root6Node14Domains3_fast_eq root6Node14Domains4_fast_eq
    root6Node14Step4Narrowing_checked (by decide)
def root6Node15Domains0 : Domains 91 State := restrict root6Node14Domains4 6 (1,2)
def root6Node15Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,3)]
  | 2 => some [(4,5),(7,5),(8,5)]
  | 3 => some [(1,0),(6,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(7,5),(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5)]
  | 16 => some [(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(8,0)]
  | 22 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(7,1),(8,4)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(2,5),(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(7,4),(8,0)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,1),(8,4)]
  | 63 => some [(0,1),(6,4),(6,5)]
  | 64 => some [(0,4),(1,2),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(5,5),(7,5),(8,5)]
  | 72 => some [(0,3),(1,0),(7,0)]
  | 73 => some [(4,3),(7,1),(8,1)]
  | 74 => some [(1,5),(3,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(1,3),(6,2),(6,3)]
theorem root6Node15Domains0_fast_eq : root6Node15Domains0 = expandDomains root6Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node15Domains0 v = expandDomains root6Node15Domains0Fast v from by decide) v
def root6Node15Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2),(5,2),(8,2)]
  | 1 => [(5,0),(5,3)]
  | 2 => [(4,5),(8,5)]
  | 3 => [(1,0),(7,0)]
  | 4 => [(4,3),(7,1),(8,3)]
  | 5 => [(1,5),(7,5),(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0)]
  | 11 => [(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(1,5),(6,5)]
  | 16 => [(0,4),(1,1),(6,1)]
  | 17 => [(5,1),(5,4),(8,1)]
  | 18 => [(0,0),(0,1),(6,4),(6,5)]
  | 19 => [(0,4),(1,2),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,4),(7,4)]
  | 21 => [(2,2),(2,4),(4,2)]
  | 22 => [(1,3),(3,3),(5,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => [(0,2),(1,5),(3,5),(6,0)]
  | 30 => [(0,4),(1,1),(7,1)]
  | 31 => [(0,1),(1,4),(6,5)]
  | 32 => [(0,4),(0,5),(6,2)]
  | 33 => [(4,4),(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(2,5),(4,5)]
  | 42 => [(1,0),(6,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5),(7,5)]
  | 48 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(6,4),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0),(7,4)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(1,0),(4,2),(7,0),(8,2)]
  | 59 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => [(4,5),(7,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1),(8,1)]
  | 63 => [(0,1),(6,5)]
  | 64 => [(0,4),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0),(6,4)]
  | 67 => [(1,2),(7,2)]
  | 68 => [(4,0),(7,4),(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(7,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(1,0),(7,0)]
  | 73 => [(4,3),(7,1)]
  | 74 => [(1,5),(3,5),(7,5)]
  | 75 => [(0,3),(6,1)]
  | 76 => [(4,1),(5,1),(8,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5)]
  | 78 => [(0,5),(1,3),(6,3),(7,3)]
  | 79 => [(4,2),(4,4),(7,2),(8,2)]
  | 80 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(1,3),(6,2),(6,3)]
def root6Node15Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(8,2)]
  | 1 => some [(5,0),(5,3)]
  | 2 => some [(4,5),(8,5)]
  | 3 => some [(1,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(7,5),(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5)]
  | 16 => some [(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(1,3),(3,3),(5,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5),(4,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5),(3,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(1,3),(6,2),(6,3)]
theorem root6Node15Domains1_fast_eq : root6Node15Domains1 = expandDomains root6Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node15Domains1 v = expandDomains root6Node15Domains1Fast v from by decide) v
theorem root6Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq (by decide)
theorem root6Node15Step1Narrowing_checked :
    checkNarrowing table33 root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root6Node15Domains0 root6Node15Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node15Step1Chunk0_0_checked, root6Node15Step1Chunk0_1_checked, root6Node15Step1Chunk0_2_checked, root6Node15Step1Chunk0_3_checked, root6Node15Step1Chunk0_4_checked, root6Node15Step1Chunk0_5_checked, root6Node15Step1Chunk1_0_checked, root6Node15Step1Chunk1_1_checked, root6Node15Step1Chunk1_2_checked, root6Node15Step1Chunk1_3_checked, root6Node15Step1Chunk1_4_checked, root6Node15Step1Chunk1_5_checked, root6Node15Step1Chunk2_0_checked, root6Node15Step1Chunk2_1_checked, root6Node15Step1Chunk2_2_checked, root6Node15Step1Chunk2_3_checked, root6Node15Step1Chunk2_4_checked, root6Node15Step1Chunk2_5_checked, root6Node15Step1Chunk3_0_checked, root6Node15Step1Chunk3_1_checked, root6Node15Step1Chunk3_2_checked, root6Node15Step1Chunk3_3_checked, root6Node15Step1Chunk3_4_checked, root6Node15Step1Chunk3_5_checked, root6Node15Step1Chunk4_0_checked, root6Node15Step1Chunk4_1_checked, root6Node15Step1Chunk4_2_checked, root6Node15Step1Chunk4_3_checked, root6Node15Step1Chunk4_4_checked, root6Node15Step1Chunk4_5_checked, root6Node15Step1Chunk5_0_checked, root6Node15Step1Chunk5_1_checked, root6Node15Step1Chunk5_2_checked, root6Node15Step1Chunk5_3_checked, root6Node15Step1Chunk5_4_checked, root6Node15Step1Chunk5_5_checked, root6Node15Step1Chunk6_0_checked, root6Node15Step1Chunk6_1_checked, root6Node15Step1Chunk6_2_checked, root6Node15Step1Chunk6_3_checked, root6Node15Step1Chunk6_4_checked, root6Node15Step1Chunk6_5_checked, root6Node15Step1Chunk7_0_checked, root6Node15Step1Chunk7_1_checked, root6Node15Step1Chunk7_2_checked, root6Node15Step1Chunk7_3_checked, root6Node15Step1Chunk7_4_checked, root6Node15Step1Chunk7_5_checked, root6Node15Step1Chunk8_0_checked, root6Node15Step1Chunk8_1_checked, root6Node15Step1Chunk8_2_checked, root6Node15Step1Chunk8_3_checked, root6Node15Step1Chunk8_4_checked, root6Node15Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node15Step1_checked :
    checkReplacement table33 root6Node15Domains0 root6Node15Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node15Domains0 root6Node15Domains1
    root6Node15Domains0Fast root6Node15Domains1Fast
    root6Node15Domains0_fast_eq root6Node15Domains1_fast_eq
    root6Node15Step1Narrowing_checked (by decide)
def root6Node15Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2),(5,2),(8,2)]
  | 1 => [(5,0),(5,3)]
  | 2 => [(4,5),(8,5)]
  | 3 => [(1,0),(7,0)]
  | 4 => [(4,3),(7,1),(8,3)]
  | 5 => [(1,5),(7,5),(8,5)]
  | 6 => [(1,2)]
  | 7 => [(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0)]
  | 11 => [(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(8,2)]
  | 13 => [(0,3)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(1,5),(6,5)]
  | 16 => [(0,4),(1,1),(6,1)]
  | 17 => [(5,1),(5,4),(8,1)]
  | 18 => [(0,0),(0,1),(6,4),(6,5)]
  | 19 => [(0,4),(1,2),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,4),(7,4)]
  | 21 => [(2,2),(2,4),(4,2)]
  | 22 => [(1,3),(3,3),(5,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => [(0,2),(1,5),(3,5),(6,0)]
  | 30 => [(0,4),(1,1),(7,1)]
  | 31 => [(0,1),(1,4),(6,5)]
  | 32 => [(0,4),(0,5),(6,2)]
  | 33 => [(4,4),(5,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(8,0)]
  | 40 => [(3,0),(5,0)]
  | 41 => [(2,5),(4,5)]
  | 42 => [(1,0),(6,0),(7,0)]
  | 43 => [(4,3),(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5),(7,5)]
  | 48 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(6,4),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0),(7,4)]
  | 54 => [(1,3),(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0),(8,0)]
  | 57 => [(4,5),(7,3)]
  | 58 => [(1,0),(4,2),(7,0),(8,2)]
  | 59 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => [(4,5),(7,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1),(8,1)]
  | 63 => [(0,1),(6,5)]
  | 64 => [(0,4),(6,2)]
  | 65 => [(5,4),(8,4)]
  | 66 => [(0,0),(6,4)]
  | 67 => [(1,2),(7,2)]
  | 68 => [(4,0),(7,4),(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(7,3)]
  | 70 => [(8,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(1,0),(7,0)]
  | 73 => [(4,3),(7,1)]
  | 74 => [(1,5),(3,5),(7,5)]
  | 75 => [(0,3),(6,1)]
  | 76 => [(4,1),(5,1),(8,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5)]
  | 78 => [(0,5),(1,3),(6,3)]
  | 79 => [(4,4),(7,2),(8,2)]
  | 80 => [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 81 => [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => [(5,2),(5,5),(8,5)]
  | 85 => [(0,4),(1,1),(7,1)]
  | 86 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 87 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 88 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 89 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root6Node15Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(8,2)]
  | 1 => some [(5,0),(5,3)]
  | 2 => some [(4,5),(8,5)]
  | 3 => some [(1,0),(7,0)]
  | 4 => some [(4,3),(7,1),(8,3)]
  | 5 => some [(1,5),(7,5),(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5)]
  | 16 => some [(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,4),(7,4)]
  | 21 => some [(2,2),(2,4),(4,2)]
  | 22 => some [(1,3),(3,3),(5,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4),(1,1),(7,1)]
  | 31 => some [(0,1),(1,4),(6,5)]
  | 32 => some [(0,4),(0,5),(6,2)]
  | 33 => some [(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(8,0)]
  | 40 => some [(3,0),(5,0)]
  | 41 => some [(2,5),(4,5)]
  | 42 => some [(1,0),(6,0),(7,0)]
  | 43 => some [(4,3),(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0),(7,4)]
  | 54 => some [(1,3),(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 60 => some [(4,5),(7,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1),(8,1)]
  | 63 => some [(0,1),(6,5)]
  | 64 => some [(0,4),(6,2)]
  | 65 => some [(5,4),(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(7,3)]
  | 70 => some [(8,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(1,0),(7,0)]
  | 73 => some [(4,3),(7,1)]
  | 74 => some [(1,5),(3,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(4,1),(5,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5)]
  | 78 => some [(0,5),(1,3),(6,3)]
  | 79 => some [(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | 83 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 84 => some [(5,2),(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(7,1)]
  | 86 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root6Node15Domains2_fast_eq : root6Node15Domains2 = expandDomains root6Node15Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node15Domains2 v = expandDomains root6Node15Domains2Fast v from by decide) v
theorem root6Node15Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq (by decide)
theorem root6Node15Step2Narrowing_checked :
    checkNarrowing table65 root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root6Node15Domains1 root6Node15Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node15Step2Chunk0_0_checked, root6Node15Step2Chunk0_1_checked, root6Node15Step2Chunk0_2_checked, root6Node15Step2Chunk0_3_checked, root6Node15Step2Chunk0_4_checked, root6Node15Step2Chunk0_5_checked, root6Node15Step2Chunk1_0_checked, root6Node15Step2Chunk1_1_checked, root6Node15Step2Chunk1_2_checked, root6Node15Step2Chunk1_3_checked, root6Node15Step2Chunk1_4_checked, root6Node15Step2Chunk1_5_checked, root6Node15Step2Chunk2_0_checked, root6Node15Step2Chunk2_1_checked, root6Node15Step2Chunk2_2_checked, root6Node15Step2Chunk2_3_checked, root6Node15Step2Chunk2_4_checked, root6Node15Step2Chunk2_5_checked, root6Node15Step2Chunk3_0_checked, root6Node15Step2Chunk3_1_checked, root6Node15Step2Chunk3_2_checked, root6Node15Step2Chunk3_3_checked, root6Node15Step2Chunk3_4_checked, root6Node15Step2Chunk3_5_checked, root6Node15Step2Chunk4_0_checked, root6Node15Step2Chunk4_1_checked, root6Node15Step2Chunk4_2_checked, root6Node15Step2Chunk4_3_checked, root6Node15Step2Chunk4_4_checked, root6Node15Step2Chunk4_5_checked, root6Node15Step2Chunk5_0_checked, root6Node15Step2Chunk5_1_checked, root6Node15Step2Chunk5_2_checked, root6Node15Step2Chunk5_3_checked, root6Node15Step2Chunk5_4_checked, root6Node15Step2Chunk5_5_checked, root6Node15Step2Chunk6_0_checked, root6Node15Step2Chunk6_1_checked, root6Node15Step2Chunk6_2_checked, root6Node15Step2Chunk6_3_checked, root6Node15Step2Chunk6_4_checked, root6Node15Step2Chunk6_5_checked, root6Node15Step2Chunk7_0_checked, root6Node15Step2Chunk7_1_checked, root6Node15Step2Chunk7_2_checked, root6Node15Step2Chunk7_3_checked, root6Node15Step2Chunk7_4_checked, root6Node15Step2Chunk7_5_checked, root6Node15Step2Chunk8_0_checked, root6Node15Step2Chunk8_1_checked, root6Node15Step2Chunk8_2_checked, root6Node15Step2Chunk8_3_checked, root6Node15Step2Chunk8_4_checked, root6Node15Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node15Step2_checked :
    checkReplacement table65 root6Node15Domains1 root6Node15Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node15Domains1 root6Node15Domains2
    root6Node15Domains1Fast root6Node15Domains2Fast
    root6Node15Domains1_fast_eq root6Node15Domains2_fast_eq
    root6Node15Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
