module

public import SpectreFinite.RadiusFiveRoot4Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node46Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => [(1,2),(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(6,3)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => [(0,3),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5)]
  | 10 => [(0,2),(6,0)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(5,1),(7,5),(8,1)]
  | 13 => [(0,0),(1,4),(6,4),(7,4)]
  | 14 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => [(2,0),(2,2),(4,0)]
  | 16 => [(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,5),(4,1),(7,5)]
  | 22 => [(0,2),(0,3),(6,0),(6,1)]
  | 23 => [(1,1),(3,1),(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(7,4),(8,4)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(5,2),(7,0),(8,2)]
  | 32 => [(5,0),(5,3),(8,3)]
  | 33 => [(4,5),(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(6,5),(7,5)]
  | 40 => [(0,0),(0,1),(6,3),(6,4)]
  | 41 => [(1,2),(6,2),(7,2)]
  | 42 => [(7,4),(8,4)]
  | 43 => [(0,0),(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(4,2),(7,0),(8,2)]
  | 51 => [(0,3),(1,0),(1,1),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5)]
  | 54 => [(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => [(4,5),(5,2),(5,5),(8,5)]
  | 63 => [(7,0),(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => [(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0)]
  | 78 => [(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => [(1,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node46Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5)]
  | 10 => some [(0,2),(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => some [(2,0),(2,2),(4,0)]
  | 16 => some [(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,5),(4,1),(7,5)]
  | 22 => some [(0,2),(0,3),(6,0),(6,1)]
  | 23 => some [(1,1),(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(5,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(6,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,3),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
  | 78 => some [(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node46Domains3_fast_eq : root4Node46Domains3 = expandDomains root4Node46Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node46Domains3 v = expandDomains root4Node46Domains3Fast v from by decide) v
theorem root4Node46Step3Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq (by decide)
theorem root4Node46Step3Narrowing_checked :
    checkNarrowing table57 root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root4Node46Domains2 root4Node46Domains3 (by
      simp only [List.all_cons, List.all_nil, root4Node46Step3Chunk0_0_checked, root4Node46Step3Chunk0_1_checked, root4Node46Step3Chunk0_2_checked, root4Node46Step3Chunk0_3_checked, root4Node46Step3Chunk0_4_checked, root4Node46Step3Chunk0_5_checked, root4Node46Step3Chunk1_0_checked, root4Node46Step3Chunk1_1_checked, root4Node46Step3Chunk1_2_checked, root4Node46Step3Chunk1_3_checked, root4Node46Step3Chunk1_4_checked, root4Node46Step3Chunk1_5_checked, root4Node46Step3Chunk2_0_checked, root4Node46Step3Chunk2_1_checked, root4Node46Step3Chunk2_2_checked, root4Node46Step3Chunk2_3_checked, root4Node46Step3Chunk2_4_checked, root4Node46Step3Chunk2_5_checked, root4Node46Step3Chunk3_0_checked, root4Node46Step3Chunk3_1_checked, root4Node46Step3Chunk3_2_checked, root4Node46Step3Chunk3_3_checked, root4Node46Step3Chunk3_4_checked, root4Node46Step3Chunk3_5_checked, root4Node46Step3Chunk4_0_checked, root4Node46Step3Chunk4_1_checked, root4Node46Step3Chunk4_2_checked, root4Node46Step3Chunk4_3_checked, root4Node46Step3Chunk4_4_checked, root4Node46Step3Chunk4_5_checked, root4Node46Step3Chunk5_0_checked, root4Node46Step3Chunk5_1_checked, root4Node46Step3Chunk5_2_checked, root4Node46Step3Chunk5_3_checked, root4Node46Step3Chunk5_4_checked, root4Node46Step3Chunk5_5_checked, root4Node46Step3Chunk6_0_checked, root4Node46Step3Chunk6_1_checked, root4Node46Step3Chunk6_2_checked, root4Node46Step3Chunk6_3_checked, root4Node46Step3Chunk6_4_checked, root4Node46Step3Chunk6_5_checked, root4Node46Step3Chunk7_0_checked, root4Node46Step3Chunk7_1_checked, root4Node46Step3Chunk7_2_checked, root4Node46Step3Chunk7_3_checked, root4Node46Step3Chunk7_4_checked, root4Node46Step3Chunk7_5_checked, root4Node46Step3Chunk8_0_checked, root4Node46Step3Chunk8_1_checked, root4Node46Step3Chunk8_2_checked, root4Node46Step3Chunk8_3_checked, root4Node46Step3Chunk8_4_checked, root4Node46Step3Chunk8_5_checked, Bool.true_and])
theorem root4Node46Step3_checked :
    checkReplacement table57 root4Node46Domains2 root4Node46Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root4Node46Domains2 root4Node46Domains3
    root4Node46Domains2Fast root4Node46Domains3Fast
    root4Node46Domains2_fast_eq root4Node46Domains3_fast_eq
    root4Node46Step3Narrowing_checked (by decide)
def root4Node46Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => [(1,2),(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(6,3)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => [(0,3),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5)]
  | 10 => [(0,2),(6,0)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(5,1),(7,5),(8,1)]
  | 13 => [(0,0),(1,4),(6,4),(7,4)]
  | 14 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => [(2,0),(2,2),(4,0)]
  | 16 => [(3,3),(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,5),(4,1),(7,5)]
  | 22 => [(0,2),(0,3),(6,0),(6,1)]
  | 23 => [(1,1),(3,1),(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(7,4),(8,4)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(5,2),(7,0),(8,2)]
  | 32 => [(5,0),(5,3),(8,3)]
  | 33 => [(4,5),(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(6,5),(7,5)]
  | 40 => [(0,0),(0,1),(6,3),(6,4)]
  | 41 => [(1,2),(6,2),(7,2)]
  | 42 => [(7,4),(8,4)]
  | 43 => [(0,0),(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(4,2),(7,0),(8,2)]
  | 51 => [(0,3),(1,0),(1,1),(6,1)]
  | 52 => [(4,1),(7,1),(8,1)]
  | 53 => [(0,2),(1,5)]
  | 54 => [(1,1),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => [(4,5),(5,2),(5,5),(8,5)]
  | 63 => [(7,0),(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5),(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,1)]
  | 70 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => [(4,4),(5,4),(7,2),(8,4)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(1,3),(6,3)]
  | 74 => [(4,4),(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0)]
  | 78 => [(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => [(1,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node46Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5)]
  | 10 => some [(0,2),(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => some [(2,0),(2,2),(4,0)]
  | 16 => some [(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,5),(4,1),(7,5)]
  | 22 => some [(0,2),(0,3),(6,0),(6,1)]
  | 23 => some [(1,1),(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(5,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(6,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,3),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
  | 78 => some [(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node46Domains4_fast_eq : root4Node46Domains4 = expandDomains root4Node46Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node46Domains4 v = expandDomains root4Node46Domains4Fast v from by decide) v
theorem root4Node46Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq (by decide)
theorem root4Node46Step4Narrowing_checked :
    checkNarrowing table0 root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root4Node46Domains3 root4Node46Domains4 (by
      simp only [List.all_cons, List.all_nil, root4Node46Step4Chunk0_0_checked, root4Node46Step4Chunk0_1_checked, root4Node46Step4Chunk0_2_checked, root4Node46Step4Chunk0_3_checked, root4Node46Step4Chunk0_4_checked, root4Node46Step4Chunk0_5_checked, root4Node46Step4Chunk1_0_checked, root4Node46Step4Chunk1_1_checked, root4Node46Step4Chunk1_2_checked, root4Node46Step4Chunk1_3_checked, root4Node46Step4Chunk1_4_checked, root4Node46Step4Chunk1_5_checked, root4Node46Step4Chunk2_0_checked, root4Node46Step4Chunk2_1_checked, root4Node46Step4Chunk2_2_checked, root4Node46Step4Chunk2_3_checked, root4Node46Step4Chunk2_4_checked, root4Node46Step4Chunk2_5_checked, root4Node46Step4Chunk3_0_checked, root4Node46Step4Chunk3_1_checked, root4Node46Step4Chunk3_2_checked, root4Node46Step4Chunk3_3_checked, root4Node46Step4Chunk3_4_checked, root4Node46Step4Chunk3_5_checked, root4Node46Step4Chunk4_0_checked, root4Node46Step4Chunk4_1_checked, root4Node46Step4Chunk4_2_checked, root4Node46Step4Chunk4_3_checked, root4Node46Step4Chunk4_4_checked, root4Node46Step4Chunk4_5_checked, root4Node46Step4Chunk5_0_checked, root4Node46Step4Chunk5_1_checked, root4Node46Step4Chunk5_2_checked, root4Node46Step4Chunk5_3_checked, root4Node46Step4Chunk5_4_checked, root4Node46Step4Chunk5_5_checked, root4Node46Step4Chunk6_0_checked, root4Node46Step4Chunk6_1_checked, root4Node46Step4Chunk6_2_checked, root4Node46Step4Chunk6_3_checked, root4Node46Step4Chunk6_4_checked, root4Node46Step4Chunk6_5_checked, root4Node46Step4Chunk7_0_checked, root4Node46Step4Chunk7_1_checked, root4Node46Step4Chunk7_2_checked, root4Node46Step4Chunk7_3_checked, root4Node46Step4Chunk7_4_checked, root4Node46Step4Chunk7_5_checked, root4Node46Step4Chunk8_0_checked, root4Node46Step4Chunk8_1_checked, root4Node46Step4Chunk8_2_checked, root4Node46Step4Chunk8_3_checked, root4Node46Step4Chunk8_4_checked, root4Node46Step4Chunk8_5_checked, Bool.true_and])
theorem root4Node46Step4_checked :
    checkReplacement table0 root4Node46Domains3 root4Node46Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root4Node46Domains3 root4Node46Domains4
    root4Node46Domains3Fast root4Node46Domains4Fast
    root4Node46Domains3_fast_eq root4Node46Domains4_fast_eq
    root4Node46Step4Narrowing_checked (by decide)
def root4Node47Domains0 : Domains 91 State := restrict root4Node46Domains4 3 (1,4)
def root4Node47Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5)]
  | 10 => some [(0,2),(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 15 => some [(2,0),(2,2),(4,0)]
  | 16 => some [(3,3),(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,5),(4,1),(7,5)]
  | 22 => some [(0,2),(0,3),(6,0),(6,1)]
  | 23 => some [(1,1),(3,1),(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(5,2),(7,0),(8,2)]
  | 32 => some [(5,0),(5,3),(8,3)]
  | 33 => some [(4,5),(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(6,5),(7,5)]
  | 40 => some [(0,0),(0,1),(6,3),(6,4)]
  | 41 => some [(1,2),(6,2),(7,2)]
  | 42 => some [(7,4),(8,4)]
  | 43 => some [(0,0),(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5)]
  | 54 => some [(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 62 => some [(4,5),(5,2),(5,5),(8,5)]
  | 63 => some [(7,0),(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 71 => some [(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
  | 78 => some [(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node47Domains0_fast_eq : root4Node47Domains0 = expandDomains root4Node47Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node47Domains0 v = expandDomains root4Node47Domains0Fast v from by decide) v
def root4Node47Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5),(6,3)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(2,5),(4,5)]
  | 7 => [(1,0),(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(5,1),(7,5),(8,1)]
  | 13 => [(0,0)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3),(8,3)]
  | 20 => [(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(4,4),(7,4),(8,4)]
  | 30 => [(4,5),(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(7,1),(8,1)]
  | 39 => [(1,5),(6,5),(7,5)]
  | 40 => [(0,0),(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,5)]
  | 50 => [(4,2),(7,0),(8,2)]
  | 51 => [(1,1),(6,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(6,3),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(7,3)]
  | 62 => [(5,2)]
  | 63 => [(8,0)]
  | 64 => [(8,3)]
  | 65 => [(5,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,1)]
  | 70 => [(6,2)]
  | 71 => [(8,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(4,4)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0)]
  | 78 => [(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => [(1,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node47Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
  | 13 => some [(0,0)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(4,4),(7,4),(8,4)]
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(7,1),(8,1)]
  | 39 => some [(1,5),(6,5),(7,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,5)]
  | 50 => some [(4,2),(7,0),(8,2)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(6,3),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(7,3)]
  | 62 => some [(5,2)]
  | 63 => some [(8,0)]
  | 64 => some [(8,3)]
  | 65 => some [(5,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,1)]
  | 70 => some [(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(4,4)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0)]
  | 78 => some [(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node47Domains1_fast_eq : root4Node47Domains1 = expandDomains root4Node47Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node47Domains1 v = expandDomains root4Node47Domains1Fast v from by decide) v
theorem root4Node47Step1Chunk0_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk0_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk1_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk2_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk3_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk4_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk5_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk6_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq (by decide)
theorem root4Node47Step1Narrowing_checked :
    checkNarrowing table33 root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root4Node47Domains0 root4Node47Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node47Step1Chunk0_0_checked, root4Node47Step1Chunk0_1_checked, root4Node47Step1Chunk0_2_checked, root4Node47Step1Chunk0_3_checked, root4Node47Step1Chunk0_4_checked, root4Node47Step1Chunk0_5_checked, root4Node47Step1Chunk1_0_checked, root4Node47Step1Chunk1_1_checked, root4Node47Step1Chunk1_2_checked, root4Node47Step1Chunk1_3_checked, root4Node47Step1Chunk1_4_checked, root4Node47Step1Chunk1_5_checked, root4Node47Step1Chunk2_0_checked, root4Node47Step1Chunk2_1_checked, root4Node47Step1Chunk2_2_checked, root4Node47Step1Chunk2_3_checked, root4Node47Step1Chunk2_4_checked, root4Node47Step1Chunk2_5_checked, root4Node47Step1Chunk3_0_checked, root4Node47Step1Chunk3_1_checked, root4Node47Step1Chunk3_2_checked, root4Node47Step1Chunk3_3_checked, root4Node47Step1Chunk3_4_checked, root4Node47Step1Chunk3_5_checked, root4Node47Step1Chunk4_0_checked, root4Node47Step1Chunk4_1_checked, root4Node47Step1Chunk4_2_checked, root4Node47Step1Chunk4_3_checked, root4Node47Step1Chunk4_4_checked, root4Node47Step1Chunk4_5_checked, root4Node47Step1Chunk5_0_checked, root4Node47Step1Chunk5_1_checked, root4Node47Step1Chunk5_2_checked, root4Node47Step1Chunk5_3_checked, root4Node47Step1Chunk5_4_checked, root4Node47Step1Chunk5_5_checked, root4Node47Step1Chunk6_0_checked, root4Node47Step1Chunk6_1_checked, root4Node47Step1Chunk6_2_checked, root4Node47Step1Chunk6_3_checked, root4Node47Step1Chunk6_4_checked, root4Node47Step1Chunk6_5_checked, root4Node47Step1Chunk7_0_checked, root4Node47Step1Chunk7_1_checked, root4Node47Step1Chunk7_2_checked, root4Node47Step1Chunk7_3_checked, root4Node47Step1Chunk7_4_checked, root4Node47Step1Chunk7_5_checked, root4Node47Step1Chunk8_0_checked, root4Node47Step1Chunk8_1_checked, root4Node47Step1Chunk8_2_checked, root4Node47Step1Chunk8_3_checked, root4Node47Step1Chunk8_4_checked, root4Node47Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node47Step1_checked :
    checkReplacement table33 root4Node47Domains0 root4Node47Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node47Domains0 root4Node47Domains1
    root4Node47Domains0Fast root4Node47Domains1Fast
    root4Node47Domains0_fast_eq root4Node47Domains1_fast_eq
    root4Node47Step1Narrowing_checked (by decide)
def root4Node47Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4)]
  | 1 => [(0,5),(6,2)]
  | 2 => [(4,4),(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5),(6,3)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(2,5),(4,5)]
  | 7 => [(1,0),(6,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(6,0)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(5,1),(7,5),(8,1)]
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
  | 30 => [(4,5),(8,5)]
  | 31 => [(7,0)]
  | 32 => [(8,3)]
  | 33 => [(8,5)]
  | 34 => [(1,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(8,1)]
  | 39 => [(1,5),(6,5)]
  | 40 => [(0,0),(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(6,3)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(7,0)]
  | 51 => [(1,1),(6,1)]
  | 52 => [(4,1)]
  | 53 => [(0,2)]
  | 54 => [(1,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(7,3)]
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
  | 78 => [(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(1,5)]
  | 83 => [(6,1)]
  | 84 => [(5,1)]
  | 85 => [(1,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(8,3)]
def root4Node47Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4)]
  | 1 => some [(0,5),(6,2)]
  | 2 => some [(4,4),(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(2,5),(4,5)]
  | 7 => some [(1,0),(6,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(6,0)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(5,1),(7,5),(8,1)]
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
  | 30 => some [(4,5),(8,5)]
  | 31 => some [(7,0)]
  | 32 => some [(8,3)]
  | 33 => some [(8,5)]
  | 34 => some [(1,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(8,1)]
  | 39 => some [(1,5),(6,5)]
  | 40 => some [(0,0),(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(6,3)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(7,0)]
  | 51 => some [(1,1),(6,1)]
  | 52 => some [(4,1)]
  | 53 => some [(0,2)]
  | 54 => some [(1,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(7,3)]
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
  | 78 => some [(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(1,5)]
  | 83 => some [(6,1)]
  | 84 => some [(5,1)]
  | 85 => some [(1,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(8,3)]
theorem root4Node47Domains2_fast_eq : root4Node47Domains2 = expandDomains root4Node47Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node47Domains2 v = expandDomains root4Node47Domains2Fast v from by decide) v
theorem root4Node47Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq (by decide)
theorem root4Node47Step2Narrowing_checked :
    checkNarrowing table57 root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root4Node47Domains1 root4Node47Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node47Step2Chunk0_0_checked, root4Node47Step2Chunk0_1_checked, root4Node47Step2Chunk0_2_checked, root4Node47Step2Chunk0_3_checked, root4Node47Step2Chunk0_4_checked, root4Node47Step2Chunk0_5_checked, root4Node47Step2Chunk1_0_checked, root4Node47Step2Chunk1_1_checked, root4Node47Step2Chunk1_2_checked, root4Node47Step2Chunk1_3_checked, root4Node47Step2Chunk1_4_checked, root4Node47Step2Chunk1_5_checked, root4Node47Step2Chunk2_0_checked, root4Node47Step2Chunk2_1_checked, root4Node47Step2Chunk2_2_checked, root4Node47Step2Chunk2_3_checked, root4Node47Step2Chunk2_4_checked, root4Node47Step2Chunk2_5_checked, root4Node47Step2Chunk3_0_checked, root4Node47Step2Chunk3_1_checked, root4Node47Step2Chunk3_2_checked, root4Node47Step2Chunk3_3_checked, root4Node47Step2Chunk3_4_checked, root4Node47Step2Chunk3_5_checked, root4Node47Step2Chunk4_0_checked, root4Node47Step2Chunk4_1_checked, root4Node47Step2Chunk4_2_checked, root4Node47Step2Chunk4_3_checked, root4Node47Step2Chunk4_4_checked, root4Node47Step2Chunk4_5_checked, root4Node47Step2Chunk5_0_checked, root4Node47Step2Chunk5_1_checked, root4Node47Step2Chunk5_2_checked, root4Node47Step2Chunk5_3_checked, root4Node47Step2Chunk5_4_checked, root4Node47Step2Chunk5_5_checked, root4Node47Step2Chunk6_0_checked, root4Node47Step2Chunk6_1_checked, root4Node47Step2Chunk6_2_checked, root4Node47Step2Chunk6_3_checked, root4Node47Step2Chunk6_4_checked, root4Node47Step2Chunk6_5_checked, root4Node47Step2Chunk7_0_checked, root4Node47Step2Chunk7_1_checked, root4Node47Step2Chunk7_2_checked, root4Node47Step2Chunk7_3_checked, root4Node47Step2Chunk7_4_checked, root4Node47Step2Chunk7_5_checked, root4Node47Step2Chunk8_0_checked, root4Node47Step2Chunk8_1_checked, root4Node47Step2Chunk8_2_checked, root4Node47Step2Chunk8_3_checked, root4Node47Step2Chunk8_4_checked, root4Node47Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node47Step2_checked :
    checkReplacement table57 root4Node47Domains1 root4Node47Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node47Domains1 root4Node47Domains2
    root4Node47Domains1Fast root4Node47Domains2Fast
    root4Node47Domains1_fast_eq root4Node47Domains2_fast_eq
    root4Node47Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
